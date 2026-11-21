"""
Oyun Dublaj - ekrandaki altyazıyı okur, Türkçeye çevirir, karaktere uygun sesle seslendirir.

Akış:  ekran yakalama -> OCR (easyocr) -> Claude (çeviri + konuşan/cinsiyet/yaş/duygu tahmini)
       -> edge-tts (Türkçe nöral ses) -> hoparlör

Kurulum:  pip install -r requirements.txt
Anahtar:  ANTHROPIC_API_KEY ortam değişkenini ayarlayın.
Oyunu "Kenarlıksız pencere" (borderless) modunda çalıştırın ki seçim ekranı görünsün.
"""
import sys
import os

if sys.stdout is None:               # --noconsole ile derlenince easyocr/tqdm çökmesin
    sys.stdout = open(os.devnull, "w")
if sys.stderr is None:
    sys.stderr = open(os.devnull, "w")

import asyncio
import ctypes
import hashlib
import difflib
import json
import os
import queue
import re
import tempfile
import threading
import time
import tkinter as tk
import uuid
from collections import deque
from tkinter import scrolledtext

import mss
import numpy as np

MODEL = "claude-haiku-5-5"          # hızlı ve ucuz; kaliteyi artırmak için claude-sonnet-5-5
KAYNAK_DIL = ["en"]                 # oyunun altyazı dili (easyocr kodu): en, de, fr, ru ...
TARAMA_ARALIGI = 0.6                # saniye
KARAKTER_DOSYASI = "karakterler.json"

SESLER = {"erkek": "tr-TR-AhmetNeural", "kadin": "tr-TR-EmelNeural"}
YAS_PITCH = {"genc": 4, "orta": 0, "yasli": -6}
DUYGU = {                            # rate %, pitch Hz, volume %
    "normal": (0, 0, 0),
    "ofkeli": (10, -4, 20),
    "korkmus": (15, 8, 0),
    "nese": (8, 6, 10),
    "uzgun": (-12, -6, -10),
    "fisilti": (-5, 0, -35),
}

SISTEM = """Sen bir oyun yerelleştirme ve dublaj yönetmenisin. Ekrandan OCR ile okunmuş bir oyun
altyazısı alacaksın (hatalı harfler olabilir, düzelt). Yalnızca şu JSON'u döndür, başka hiçbir şey yazma:
{"turkce": "doğal, konuşma diline uygun Türkçe çeviri",
 "konusan": "karakter adı; altyazıda yazıyorsa onu kullan, bilmiyorsan 'Bilinmeyen'",
 "cinsiyet": "erkek|kadin", "yas": "genc|orta|yasli",
 "duygu": "normal|ofkeli|korkmus|nese|uzgun|fisilti"}
Menü, tuş ipucu veya görev listesi gibi konuşma OLMAYAN metinse {"turkce": ""} döndür.
Bilinen karakterleri tutarlı kullan."""


# ---------------------------------------------------------------- yardımcılar
try:
    ctypes.windll.shcore.SetProcessDpiAwareness(1)   # Windows ölçekleme sorunu için
except Exception:
    pass


def karakter_yukle():
    try:
        with open(KARAKTER_DOSYASI, encoding="utf-8") as f:
            return json.load(f)
    except Exception:
        return {}


def karakter_kaydet(k):
    with open(KARAKTER_DOSYASI, "w", encoding="utf-8") as f:
        json.dump(k, f, ensure_ascii=False, indent=2)


def bolge_sec(root):
    """Ekranda sürükleyerek altyazı bölgesini seçtirir."""
    sonuc, d = {}, {}
    top = tk.Toplevel(root)
    top.attributes("-fullscreen", True, "-alpha", 0.3, "-topmost", True)
    c = tk.Canvas(top, cursor="cross", bg="black", highlightthickness=0)
    c.pack(fill="both", expand=True)

    def bas(e):
        d.update(x0=e.x_root, y0=e.y_root, cx=e.x, cy=e.y)
        d["r"] = c.create_rectangle(e.x, e.y, e.x, e.y, outline="red", width=2)

    def surukle(e):
        c.coords(d["r"], d["cx"], d["cy"], e.x, e.y)

    def birak(e):
        x0, y0, x1, y1 = d["x0"], d["y0"], e.x_root, e.y_root
        if abs(x1 - x0) > 20 and abs(y1 - y0) > 10:
            sonuc["b"] = {"left": min(x0, x1), "top": min(y0, y1),
                          "width": abs(x1 - x0), "height": abs(y1 - y0)}
        top.destroy()

    c.bind("<ButtonPress-1>", bas)
    c.bind("<B1-Motion>", surukle)
    c.bind("<ButtonRelease-1>", birak)
    top.bind("<Escape>", lambda e: top.destroy())
    root.wait_window(top)
    return sonuc.get("b")


# ---------------------------------------------------------------- çeviri
class Ceviri:
    def __init__(self):
        from anthropic import Anthropic
        self.client = Anthropic()
        self.gecmis = deque(maxlen=5)

    def cevir(self, metin, bilinenler):
        icerik = (f"Bilinen karakterler: {', '.join(bilinenler) or 'yok'}\n"
                  f"Önceki satırlar: {' | '.join(self.gecmis) or 'yok'}\n"
                  f"Altyazı: {metin}")
        r = self.client.messages.create(
            model=MODEL, max_tokens=400, system=SISTEM,
            messages=[{"role": "user", "content": icerik}])
        m = re.search(r"\{.*\}", r.content[0].text, re.S)
        veri = json.loads(m.group(0)) if m else {"turkce": ""}
        if veri.get("turkce"):
            self.gecmis.append(metin)
        return veri


# ---------------------------------------------------------------- ses
def ses_parametreleri(ad, profil, duygu):
    """Aynı karakter hep aynı sesi alır; karakterler arası ince ton farkı yaratır."""
    ofset = int(hashlib.md5(ad.encode()).hexdigest(), 16) % 11 - 5      # -5..+5 Hz
    ofset_hiz = int(hashlib.md5((ad + "h").encode()).hexdigest(), 16) % 9 - 4
    hiz, pitch, ses = DUYGU.get(duygu, DUYGU["normal"])
    pitch += ofset + YAS_PITCH.get(profil["yas"], 0)
    hiz += ofset_hiz
    return f"{hiz:+d}%", f"{pitch:+d}Hz", f"{ses:+d}%"


async def sesi_uret(metin, ses, hiz, pitch, seviye, yol):
    import edge_tts
    await edge_tts.Communicate(metin, ses, rate=hiz, pitch=pitch, volume=seviye).save(yol)


def cal(yol):
    import pygame
    if not pygame.mixer.get_init():
        pygame.mixer.init()
    pygame.mixer.music.load(yol)
    pygame.mixer.music.play()
    while pygame.mixer.music.get_busy():
        time.sleep(0.05)
    pygame.mixer.music.unload()


# ---------------------------------------------------------------- uygulama
class Uygulama:
    def __init__(self):
        self.root = tk.Tk()
        self.root.title("Oyun Dublaj")
        self.root.geometry("520x380")
        self.root.attributes("-topmost", True)
        if not os.environ.get("ANTHROPIC_API_KEY"):
            from tkinter import simpledialog
            anahtar = simpledialog.askstring(
                "API anahtarı", "Anthropic API anahtarınızı yapıştırın:", parent=self.root)
            if anahtar:
                os.environ["ANTHROPIC_API_KEY"] = anahtar.strip()
                try:
                    import subprocess
                    subprocess.run(["setx", "ANTHROPIC_API_KEY", anahtar.strip()],
                                   capture_output=True, creationflags=0x08000000)
                except Exception:
                    pass
        self.bolge = None
        self.calisiyor = False
        self.kuyruk = queue.Queue(maxsize=3)
        self.karakterler = karakter_yukle()
        self.ceviri = None
        self.ocr = None

        ust = tk.Frame(self.root)
        ust.pack(fill="x", padx=8, pady=6)
        tk.Button(ust, text="1) Altyazı alanını seç", command=self.sec).pack(side="left")
        self.btn = tk.Button(ust, text="2) Başlat", command=self.degistir)
        self.btn.pack(side="left", padx=8)
        self.dublaj_acik = tk.BooleanVar(value=True)
        tk.Checkbutton(ust, text="Sesli dublaj", variable=self.dublaj_acik).pack(side="left")
        self.log = scrolledtext.ScrolledText(self.root, state="disabled", wrap="word")
        self.log.pack(fill="both", expand=True, padx=8, pady=(0, 8))

    def yaz(self, s):
        def f():
            self.log.config(state="normal")
            self.log.insert("end", s + "\n")
            self.log.see("end")
            self.log.config(state="disabled")
        self.root.after(0, f)

    def sec(self):
        self.root.withdraw()
        self.root.update()
        time.sleep(0.2)
        b = bolge_sec(self.root)
        self.root.deiconify()
        if b:
            self.bolge = b
            self.yaz(f"Alan seçildi: {b['width']}x{b['height']}")

    def degistir(self):
        if self.calisiyor:
            self.calisiyor = False
            self.btn.config(text="2) Başlat")
            return
        if not self.bolge:
            self.yaz("Önce altyazı alanını seçin.")
            return
        self.calisiyor = True
        self.btn.config(text="Durdur")
        threading.Thread(target=self.tara, daemon=True).start()
        threading.Thread(target=self.seslendir, daemon=True).start()

    # --- üretici: ekran -> OCR -> çeviri
    def tara(self):
        try:
            if self.ocr is None:
                self.yaz("OCR yükleniyor (ilk seferde biraz sürer)...")
                import easyocr
                self.ocr = easyocr.Reader(KAYNAK_DIL, gpu=True)
            if self.ceviri is None:
                self.ceviri = Ceviri()
        except Exception as e:
            self.yaz(f"Başlatma hatası: {e}")
            self.calisiyor = False
            return

        self.yaz("Dinleniyor...")
        son = ""
        with mss.mss() as ekran:
            while self.calisiyor:
                try:
                    img = np.array(ekran.grab(self.bolge))[:, :, :3]
                    parcalar = self.ocr.readtext(img, detail=1, paragraph=False)
                    metin = " ".join(t for _, t, p in parcalar if p > 0.4).strip()
                    if len(metin) < 4 or difflib.SequenceMatcher(None, son, metin).ratio() > 0.85:
                        time.sleep(TARAMA_ARALIGI)
                        continue
                    son = metin
                    veri = self.ceviri.cevir(metin, list(self.karakterler))
                    tr = veri.get("turkce", "").strip()
                    if not tr:
                        continue
                    ad = veri.get("konusan") or "Bilinmeyen"
                    if ad not in self.karakterler or ad == "Bilinmeyen":
                        self.karakterler.setdefault(ad, {
                            "cinsiyet": veri.get("cinsiyet", "erkek"),
                            "yas": veri.get("yas", "orta")})
                        karakter_kaydet(self.karakterler)
                    self.yaz(f"[{ad}] {tr}")
                    if self.dublaj_acik.get():
                        if self.kuyruk.full():
                            try:
                                self.kuyruk.get_nowait()   # eski satırı at, güncele yetiş
                            except queue.Empty:
                                pass
                        self.kuyruk.put((ad, tr, veri.get("duygu", "normal")))
                except Exception as e:
                    self.yaz(f"Hata: {e}")
                    time.sleep(2)
                time.sleep(TARAMA_ARALIGI)

    # --- tüketici: TTS + oynat
    def seslendir(self):
        while self.calisiyor:
            try:
                ad, tr, duygu = self.kuyruk.get(timeout=0.5)
            except queue.Empty:
                continue
            try:
                profil = self.karakterler.get(ad, {"cinsiyet": "erkek", "yas": "orta"})
                hiz, pitch, seviye = ses_parametreleri(ad, profil, duygu)
                yol = os.path.join(tempfile.gettempdir(), f"dublaj_{uuid.uuid4().hex}.mp3")
                asyncio.run(sesi_uret(tr, SESLER.get(profil["cinsiyet"], SESLER["erkek"]),
                                      hiz, pitch, seviye, yol))
                cal(yol)
                os.remove(yol)
            except Exception as e:
                self.yaz(f"Ses hatası: {e}")

    def calistir(self):
        self.root.mainloop()


if __name__ == "__main__":
    Uygulama().calistir()
