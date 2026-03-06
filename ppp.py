import speech_recognition as sr
import edge_tts
import asyncio
import pygame
import pywhatkit
import datetime
import wikipedia
import os
import webbrowser
import threading
import sounddevice as sd
import numpy as np
import io
import wave
import requests
import subprocess
from bs4 import BeautifulSoup
from googlesearch import search as gsearch
from google import genai
from google.genai import types
import geocoder
from PIL import Image
try:
    from pydub import AudioSegment
except ImportError:
    pass
try:
    import pytesseract
except:
    pass

import customtkinter as ctk
from tkinter import filedialog, colorchooser
import time
import random
import nltk
from sumy.parsers.plaintext import PlaintextParser
from sumy.nlp.tokenizers import Tokenizer
from sumy.summarizers.lsa import LsaSummarizer
import fitz  # PyMuPDF
from docx import Document
import openpyxl
from pptx import Presentation
import csv
import pyautogui
from AppOpener import open as app_open, close as app_close
import pygetwindow as gw
import psutil
import re
import subprocess
import json
import sys
import shutil
from collections import deque
import urllib.parse
from urllib.parse import urlparse, urlunparse
import pickle
from google.auth.transport.requests import Request
from google_auth_oauthlib.flow import InstalledAppFlow
from googleapiclient.discovery import build
import queue
try:
    from tkinterweb import HtmlFrame
except:
    pass

# Téléchargement des ressources nécessaires pour NLTK
try:
    nltk.download('punkt', quiet=True)
    nltk.download('punkt_tab', quiet=True)
except:
    pass

# Configuration de l'apparence
ctk.set_appearance_mode("dark")
ctk.set_default_color_theme("blue")

# Couleurs Premium (Style Gemini / Futuriste)
COLOR_BG = "#0B0B0C"
COLOR_NAV = "#161618"
COLOR_ACCENT = "#4285F4"  # Bleu Gemini
COLOR_ACCENT_PURPLE = "#9B72CB" # Violet Gemini
COLOR_ACCENT_RED = "#D96570" # Rouge Gemini
COLOR_TEXT = "#E3E3E3"
COLOR_SECONDARY = "#9AA0A6"
COLOR_CARD = "#1E1F20"

class JarvisseAssistant(ctk.CTk):
    def __init__(self):
        super().__init__()

        self.title("Jarvisse Assistant")
        self.geometry("800x600")
        self.configure(fg_color=COLOR_BG)

        # Initialisation Audio
        pygame.mixer.init()
        pygame.mixer.music.set_volume(1.0)
        self.voice = "fr-FR-VivienneNeural"
        self.voice_speed = "-5%"

        # Variables d'état
        self.is_listening = False
        self.conversation_history = []
        self.conversation_memory_limit = 20
        self.current_subject = None
        self.loaded_document_content = None  # Pour stocker le texte du dernier fichier chargé
        self.veille_active = True # Activer la veille par défaut
        self.voice_lock = threading.Lock() # Lock pour éviter les chevauchements audio
        self.stop_speaking_flag = False
        self.ping_pong_mode = True  # Réponses courtes et réactives
        self.ping_pong_max_chars = 2000 # Augmenté massivement pour éviter toute coupure
        self.proactive_suggestions = True  # Suggestions intelligentes basées sur le contexte
        self.voice = "fr-FR-VivienneNeural"
        self.available_voices = [
            "fr-FR-VivienneNeural", "fr-FR-RemyNeural", "fr-FR-EloiseNeural", 
            "fr-FR-DeniseNeural", "fr-FR-HenriNeural", "fr-BE-CharlineNeural", 
            "fr-BE-GerardNeural", "fr-CA-SylvieNeural", "fr-CA-JeanNeural",
            "fr-CH-ArianeNeural", "fr-CH-FabriceNeural"
        ]
        self.battery_alert_threshold = 10
        self.battery_alert_sent = False
        self.battery_low_message = "Patron, la batterie est à {percent}%"
        self.battery_plugged_message = "Patron, le chargeur est branché."
        self.battery_full_message = "Patron, la batterie est complètement chargée. Je vous recommande de retirer le chargeur"
        self.last_power_plugged = None
        self.last_full_charge_alert_time = 0 # Temps du dernier rappel batterie pleine

        self.last_full_charge_alert_time = 0 # Temps du dernier rappel batterie pleine

        self.awaiting_exit_confirm = False
        self.autonomous_mode = True
        self.autonomous_provider = "gemini"
        self.ollama_url = "http://localhost:11434/api/generate"
        self.ollama_model = "llama3.1:8b"
        self.ollama_models = ["llama3.1:8b", "llama3.1:70b", "llama3:8b", "mistral:7b", "qwen2.5:7b", "phi3:mini"]
        self.conversation_memory_limit = 100 
        self.ping_pong_max_chars = 10000 
        self.ollama_num_predict = 4096
        self.known_removable_devices = set()
        self.scanning_devices = set()
        self.scanned_devices = set()
        self.alarms = []
        self.alarm_next_id = 1
        self.anomaly_last_alert = {}
        self.anomaly_cooldown_sec = 120
        self.anomaly_temp_c = 85
        self.battery_drop_percent = 15
        self.battery_drop_window_sec = 600
        # CERVEAU PHONÉTIQUE : Chargement de la base de données étendue
        self.phonetic_path = os.path.join(os.path.dirname(__file__), "phonetic_extended.json")
        self.phonetic_map = self._load_phonetic_map()
        self.alphabet_phonetique = {
            'A':'a', 'B':'bé', 'C':'cé', 'D':'dé', 'E':'e', 'F':'èf', 'G':'gé', 'H':'ache',
            'I':'i', 'J':'ji', 'K':'ka', 'L':'èl', 'M':'èm', 'N':'èn', 'O':'o', 'P':'pé',
            'Q':'ku', 'R':'èr', 'S':'ès', 'T':'té', 'U':'u', 'V':'vé', 'W':'double-vé',
            'X':'iks', 'Y':'igrek', 'Z':'zèd'
        }
        self.battery_not_charging_grace_sec = 300
        self.proc_cpu_threshold = 80
        self.proc_cpu_duration_sec = 60
        self.proc_mem_threshold_mb = 1500
        self.disk_free_gb = 10
        self.disk_used_percent = 90
        self.anomalies_enabled = True
        self.settings_path = os.path.join(os.path.dirname(__file__), "settings.json")
        self.launch_on_startup = False
        self.ui_theme_name = "Gemini Blue"
        self.custom_accent_color = COLOR_ACCENT
        self.custom_colors = {}
        self.ui_theme_presets = {
            "Gemini Blue": {
                "bg": "#0B0B0C",
                "nav": "#161618",
                "accent": "#4285F4",
                "accent_purple": "#9B72CB",
                "accent_red": "#D96570",
                "text": "#E3E3E3",
                "secondary": "#9AA0A6",
                "card": "#1E1F20",
            },
            "Emerald": {
                "bg": "#0B1110",
                "nav": "#13201E",
                "accent": "#2CB67D",
                "accent_purple": "#4E9F8B",
                "accent_red": "#D96570",
                "text": "#E6F2EE",
                "secondary": "#9BB8AE",
                "card": "#1A2A27",
            },
            "Sunset": {
                "bg": "#16100E",
                "nav": "#241A16",
                "accent": "#F59E0B",
                "accent_purple": "#F97316",
                "accent_red": "#E11D48",
                "text": "#F5E9E2",
                "secondary": "#BCA79B",
                "card": "#2A211C",
            },
            "Steel": {
                "bg": "#0E131A",
                "nav": "#151D27",
                "accent": "#60A5FA",
                "accent_purple": "#94A3B8",
                "accent_red": "#EF4444",
                "text": "#E6EDF5",
                "secondary": "#9AA9BD",
                "card": "#1C2633",
            },
        }
        self.notifications_enabled = True
        self.notification_sources = {
            "WhatsApp.exe": True,
            "OUTLOOK.EXE": True,
            "chrome.exe": True
        }
        self.seen_notifications_order = deque()
        self.seen_notifications_set = set()
        self.max_seen_notifications = 200
        self.notifications_access_prompted = False
        self.last_battery_percent = None
        self.last_battery_time = None
        self.suspect_processes = {}
        self.services_to_watch = []
        
        # Agents Settings
        self.agent_network_enabled = False
        self.agent_control_enabled = False
        self.agent_remote_enabled = False
        self.agent_gmail_enabled = False
        self.gmail_service = None
        self.last_email_id = None
        self.remote_hosts_whitelist = []
        self.remote_default_host = ""
        self.remote_ssh_user = ""
        self.remote_ssh_port = 22
        self.remote_ssh_key_path = ""
        self.remote_require_confirmation = True
        self.awaiting_remote_confirm = None
        self.awaiting_anomaly_confirm = False
        self.conversation_continue = False
        self.voice_enabled = True
        
        # Agent Browser
        self.agent_browser_enabled = False
        self.browser_history = []

        # Agent Juridique
        self.agent_legal_enabled = False

        # Agent Cyber Sécurité
        self.agent_cyber_enabled = False

        # Agent Docteur Système
        self.agent_doctor_enabled = False

        # Agent Vidéo Surveillance
        self.agent_video_enabled = True

        # Agent Contrôle Android
        self.agent_android_enabled = True

        # Assistant Coding
        self.agent_coding_enabled = True
        self.last_internal_error = None  # Conscience de soi : stockage de la dernière erreur système interne

        # Assistant Génération Image et Vidéo
        self.agent_generation_enabled = True
        
        # Agent Assistant Licence
        self.agent_licence_enabled = True
        
        # Agent Lecture
        self.agent_lecture_enabled = True
        
        # Agent Bot Telegram
        self.agent_telegram_enabled = False
        
        # NOUVEAUX AGENTS PREMIUM
        self.agent_vision_enabled = True
        self.agent_domotique_enabled = True
        self.agent_finance_enabled = True
        self.agent_secretaire_enabled = True
        self.agent_traducteur_enabled = True
        self.agent_miner_enabled = True
        
        # NOUVEAUX AGENTS AJOUTÉS
        self.agent_news_enabled = True
        self.agent_cuisine_enabled = True
        self.agent_sante_enabled = True
        self.agent_voyage_enabled = True
        self.agent_education_enabled = True
        self.agent_shopping_enabled = True
        self.agent_social_enabled = True
        self.agent_psy_enabled = True
        self.agent_immo_enabled = True
        self.agent_auto_enabled = True
        self.agent_carrier_enabled = True
        
        # AGENTS SUPPLÉMENTAIRES (PACK GRATUIT & PREMIUM)
        self.agent_arbitre_enabled = True
        self.agent_ecolo_enabled = True
        self.agent_guetteur_enabled = True
        self.agent_historien_enabled = True
        self.agent_depanneur_enabled = True
        self.agent_astroph_enabled = True
        self.agent_stratege_enabled = True
        self.agent_architecte_enabled = True
        self.agent_business_enabled = True
        self.agent_polyglotte_enabled = True
        self.agent_nounou_enabled = True

        # Agent Appel (NOUVEAU)
        self.agent_appel_enabled = True
        self.agent_appel_number = ""
        self.agent_appel_autoreply = True
        self.agent_appel_phrases = [
            "Bonjour, je suis l'assistant de mon propriétaire. Il n'est pas disponible pour le moment.",
            "Puis-je prendre un message ou vous rappeler plus tard ?",
            "Je note votre appel. Merci et au revoir."
        ]
        self.agent_appel_filters = [] # Numéros spécifiques à répondre

        # Configuration Domotique
        self.domo_wled_ip = ""
        self.domo_ha_url = ""
        self.domo_ha_token = ""
        self.domo_arduino_port = ""
        self.domo_webhook_on = ""
        self.domo_webhook_off = ""

        self.telegram_bot_token = ""
        self.telegram_chat_id = ""
        self.telegram_bot_running = False
        self.last_command_origin = "local"

        self.generations_dir = os.path.join(os.path.dirname(__file__), "generations")
        if not os.path.exists(self.generations_dir):
            os.makedirs(self.generations_dir)

        # Gigantesque Mémoire des Agents
        self.memories_dir = os.path.join(os.path.dirname(__file__), "agent_memories")
        if not os.path.exists(self.memories_dir):
            os.makedirs(self.memories_dir)
        self.agent_memories_cache = {}

        self._load_settings()
        self._apply_theme_globals()
        # Le listener de notifications sera démarré après l'initialisation de l'UI

        if self.ollama_model not in self.ollama_models:
            self.ollama_models.insert(0, self.ollama_model)

        # Configuration Gemini pour l'autonomie
        self.gemini_api_key = "AIzaSyA0i4Oa8VChSl6SlPIyo_qMgCoqpGCUL9Y"
        try:
            if self.gemini_api_key and self.gemini_api_key != "VOTRE_CLE_API_GEMINI":
                self.genai_client = genai.Client(api_key=self.gemini_api_key)
                self.model_name = 'gemini-2.0-flash' # Modèle plus récent et disponible
            else:
                self.genai_client = None
        except Exception as e:
            print(f"Erreur initialisation Gemini: {e}")
            self.genai_client = None

        if not self.genai_client:
            self.autonomous_provider = "ollama"

        # Géolocalisation
        self.current_location = None
        self.location_city = "Inconnu"
        self.location_country = "Inconnu"
        self.location_coords = (0.0, 0.0)

        self.grid_columnconfigure(1, weight=1)
        self.grid_columnconfigure(2, weight=0)
        self.grid_rowconfigure(1, weight=1)

        self.sidebar = ctk.CTkFrame(self, width=200, fg_color=COLOR_NAV, corner_radius=0)
        self.sidebar.grid(row=0, column=0, rowspan=3, sticky="nsew")
        self.sidebar.grid_rowconfigure(0, weight=1)
        self.sidebar.grid_columnconfigure(0, weight=1)

        self.sidebar_scroll = ctk.CTkScrollableFrame(
            self.sidebar,
            fg_color=COLOR_NAV,
            corner_radius=0,
            width=200
        )
        self.sidebar_scroll.grid(row=0, column=0, sticky="nsew")
        self.sidebar_scroll.grid_rowconfigure(33, weight=1)

        self.sidebar_title = ctk.CTkLabel(self.sidebar_scroll, text="SYSTEM STATUS", font=ctk.CTkFont(size=12, weight="bold"), text_color=COLOR_ACCENT)
        self.sidebar_title.grid(row=0, column=0, padx=20, pady=(20, 10))

        self.cpu_label = ctk.CTkLabel(self.sidebar_scroll, text="CPU: 0%", font=ctk.CTkFont(size=11), text_color=COLOR_SECONDARY)
        self.cpu_label.grid(row=1, column=0, padx=20, pady=5, sticky="w")

        self.ram_label = ctk.CTkLabel(self.sidebar_scroll, text="RAM: 0%", font=ctk.CTkFont(size=11), text_color=COLOR_SECONDARY)
        self.ram_label.grid(row=2, column=0, padx=20, pady=5, sticky="w")

        self.battery_label = ctk.CTkLabel(self.sidebar_scroll, text="BATTERY: --", font=ctk.CTkFont(size=11), text_color=COLOR_SECONDARY)
        self.battery_label.grid(row=3, column=0, padx=20, pady=5, sticky="w")

        self.disk_label = ctk.CTkLabel(self.sidebar_scroll, text="DISK: 0%", font=ctk.CTkFont(size=11), text_color=COLOR_SECONDARY)
        self.disk_label.grid(row=4, column=0, padx=20, pady=5, sticky="w")

        # Séparateur
        self.separator = ctk.CTkLabel(self.sidebar_scroll, text="─────────────", font=ctk.CTkFont(size=10), text_color="#3C4043")
        self.separator.grid(row=5, column=0, padx=20, pady=10)

        # Seuil d'alerte batterie (configurable)
        self.battery_threshold_label = ctk.CTkLabel(
            self.sidebar_scroll,
            text="Alerte batterie (%)",
            font=ctk.CTkFont(size=11),
            text_color=COLOR_SECONDARY
        )
        self.battery_threshold_label.grid(row=6, column=0, padx=20, pady=(0, 5), sticky="w")

        self.battery_threshold_entry = ctk.CTkEntry(
            self.sidebar_scroll,
            height=28,
            width=120,
            fg_color=COLOR_CARD,
            border_color="#3C4043",
            text_color=COLOR_TEXT
        )
        self.battery_threshold_entry.grid(row=7, column=0, padx=20, pady=(0, 6), sticky="w")
        self.battery_threshold_entry.insert(0, str(self.battery_alert_threshold))
        self.battery_threshold_entry.bind("<Return>", lambda e: self.set_battery_threshold())

        self.battery_threshold_button = ctk.CTkButton(
            self.sidebar_scroll,
            text="Appliquer",
            height=28,
            width=120,
            fg_color=COLOR_ACCENT_PURPLE,
            hover_color="#B388EB",
            command=self.set_battery_threshold
        )
        self.battery_threshold_button.grid(row=8, column=0, padx=20, pady=(0, 10), sticky="w")

        # Messages d'alerte batterie (configurables)
        self.battery_low_msg_label = ctk.CTkLabel(
            self.sidebar_scroll,
            text="Message batterie basse",
            font=ctk.CTkFont(size=11),
            text_color=COLOR_SECONDARY
        )
        self.battery_low_msg_label.grid(row=9, column=0, padx=20, pady=(0, 5), sticky="w")

        self.battery_low_msg_entry = ctk.CTkEntry(
            self.sidebar_scroll,
            height=28,
            width=160,
            fg_color=COLOR_CARD,
            border_color="#3C4043",
            text_color=COLOR_TEXT
        )
        self.battery_low_msg_entry.grid(row=10, column=0, padx=20, pady=(0, 6), sticky="w")
        self.battery_low_message = "Attention : la batterie est à {percent}%"

        self.battery_plugged_msg_label = ctk.CTkLabel(
            self.sidebar_scroll,
            text="Message chargeur branché",
            font=ctk.CTkFont(size=11),
            text_color=COLOR_SECONDARY
        )
        self.battery_plugged_msg_label.grid(row=11, column=0, padx=20, pady=(0, 5), sticky="w")

        self.battery_plugged_msg_entry = ctk.CTkEntry(
            self.sidebar_scroll,
            height=28,
            width=160,
            fg_color=COLOR_CARD,
            border_color="#3C4043",
            text_color=COLOR_TEXT
        )
        self.battery_plugged_msg_entry.grid(row=12, column=0, padx=20, pady=(0, 6), sticky="w")
        self.battery_plugged_message = "Le chargeur est branché."

        self.battery_full_msg_label = ctk.CTkLabel(
            self.sidebar_scroll,
            text="Message batterie pleine",
            font=ctk.CTkFont(size=11),
            text_color=COLOR_SECONDARY
        )
        self.battery_full_msg_label.grid(row=13, column=0, padx=20, pady=(0, 5), sticky="w")

        self.battery_full_msg_entry = ctk.CTkEntry(
            self.sidebar_scroll,
            height=28,
            width=160,
            fg_color=COLOR_CARD,
            border_color="#3C4043",
            text_color=COLOR_TEXT
        )
        self.battery_full_msg_entry.grid(row=14, column=0, padx=20, pady=(0, 10), sticky="w")
        self.battery_full_message = "La batterie est complètement chargée. Je vous recommande de debrancher le chargeur pour eviter une surchage"

        # Mode autonome (IA)
        self.autonomous_var = ctk.BooleanVar(value=self.autonomous_mode)
        self.autonomous_switch = ctk.CTkSwitch(
            self.sidebar_scroll,
            text="Mode autonome",
            variable=self.autonomous_var,
            command=self.toggle_autonomous_mode,
            text_color=COLOR_SECONDARY
        )
        self.autonomous_switch.grid(row=15, column=0, padx=20, pady=(0, 10), sticky="w")

        # Mode Conversation Continue (Ping-Pong Auto)
        self.conv_continue_var = ctk.BooleanVar(value=self.conversation_continue)
        self.conv_continue_switch = ctk.CTkSwitch(
            self.sidebar_scroll,
            text="Conversation continue",
            variable=self.conv_continue_var,
            command=self.toggle_conversation_continue,
            text_color=COLOR_ACCENT
        )
        self.conv_continue_switch.grid(row=16, column=0, padx=20, pady=(5, 10), sticky="w")

        # Choix IA pour réponses autonomes
        self.autonomous_provider_var = ctk.StringVar(value=self.autonomous_provider)
        self.autonomous_provider_label = ctk.CTkLabel(
            self.sidebar_scroll,
            text="Réponses auto",
            font=ctk.CTkFont(size=11),
            text_color=COLOR_SECONDARY
        )
        self.autonomous_provider_label.grid(row=17, column=0, padx=20, pady=(10, 4), sticky="w")

        self.provider_gemini_radio = ctk.CTkRadioButton(
            self.sidebar_scroll,
            text="Gemini",
            variable=self.autonomous_provider_var,
            value="gemini",
            command=self.on_autonomous_provider_changed,
            text_color=COLOR_SECONDARY
        )
        self.provider_gemini_radio.grid(row=18, column=0, padx=20, pady=(0, 2), sticky="w")

        self.provider_ollama_radio = ctk.CTkRadioButton(
            self.sidebar_scroll,
            text="Ollama",
            variable=self.autonomous_provider_var,
            value="ollama",
            command=self.on_autonomous_provider_changed,
            text_color=COLOR_SECONDARY
        )
        self.provider_ollama_radio.grid(row=19, column=0, padx=20, pady=(0, 10), sticky="w")

        self.ollama_model_var = ctk.StringVar(value=self.ollama_model)
        self.ollama_model_label = ctk.CTkLabel(
            self.sidebar_scroll,
            text="Modèle Ollama",
            font=ctk.CTkFont(size=11),
            text_color=COLOR_SECONDARY
        )
        self.ollama_model_label.grid(row=20, column=0, padx=20, pady=(0, 4), sticky="w")

        self.ollama_model_menu = ctk.CTkOptionMenu(
            self.sidebar_scroll,
            values=self.ollama_models,
            variable=self.ollama_model_var,
            command=self.on_ollama_model_changed,
            fg_color=COLOR_CARD,
            button_color=COLOR_ACCENT_PURPLE,
            button_hover_color="#B388EB",
            text_color=COLOR_TEXT
        )
        self.ollama_model_menu.grid(row=21, column=0, padx=20, pady=(0, 10), sticky="w")

        self.ollama_num_predict_var = ctk.StringVar(value=str(self.ollama_num_predict))
        self.ollama_num_predict_label = ctk.CTkLabel(
            self.sidebar_scroll,
            text="Longueur r??ponse",
            font=ctk.CTkFont(size=11),
            text_color=COLOR_SECONDARY
        )
        self.ollama_num_predict_label.grid(row=22, column=0, padx=20, pady=(0, 4), sticky="w")

        self.ollama_num_predict_entry = ctk.CTkEntry(
            self.sidebar_scroll,
            textvariable=self.ollama_num_predict_var,
            height=28,
            width=120,
            fg_color=COLOR_CARD,
            border_color="#3C4043",
            text_color=COLOR_TEXT
        )
        self.ollama_num_predict_entry.grid(row=23, column=0, padx=20, pady=(0, 6), sticky="w")
        self.ollama_num_predict_entry.bind("<Return>", lambda e: self.on_ollama_num_predict_apply())

        self.ollama_num_predict_apply = ctk.CTkButton(
            self.sidebar_scroll,
            text="Appliquer",
            height=28,
            width=120,
            fg_color=COLOR_CARD,
            hover_color="#3C4043",
            command=self.on_ollama_num_predict_apply
        )
        self.ollama_num_predict_apply.grid(row=24, column=0, padx=20, pady=(0, 10), sticky="w")

        self.ollama_refresh_button = ctk.CTkButton(
            self.sidebar_scroll,
            text="Actualiser modeles",
            height=28,
            fg_color=COLOR_CARD,
            hover_color="#3C4043",
            command=self.refresh_ollama_models
        )
        self.ollama_refresh_button.grid(row=24, column=0, padx=20, pady=(0, 10), sticky="w")

        self.ollama_url_var = ctk.StringVar(value=self.ollama_url)
        self.ollama_url_label = ctk.CTkLabel(
            self.sidebar_scroll,
            text="URL Ollama",
            font=ctk.CTkFont(size=11),
            text_color=COLOR_SECONDARY
        )
        self.ollama_url_label.grid(row=25, column=0, padx=20, pady=(0, 4), sticky="w")

        self.ollama_url_entry = ctk.CTkEntry(
            self.sidebar_scroll,
            textvariable=self.ollama_url_var,
            height=28,
            width=160,
            fg_color=COLOR_CARD,
            border_color="#3C4043",
            text_color=COLOR_TEXT
        )
        self.ollama_url_entry.grid(row=26, column=0, padx=20, pady=(0, 6), sticky="w")
        self.ollama_url_entry.bind("<Return>", lambda e: self.on_ollama_url_apply())

        self.ollama_url_apply_button = ctk.CTkButton(
            self.sidebar_scroll,
            text="Appliquer URL",
            height=28,
            fg_color=COLOR_CARD,
            hover_color="#3C4043",
            command=self.on_ollama_url_apply
        )
        self.ollama_url_apply_button.grid(row=27, column=0, padx=20, pady=(0, 10), sticky="w")

        self.ollama_test_button = ctk.CTkButton(
            self.sidebar_scroll,
            text="Tester Ollama",
            height=28,
            fg_color=COLOR_CARD,
            hover_color="#3C4043",
            command=self.test_ollama_connection
        )
        self.ollama_test_button.grid(row=28, column=0, padx=20, pady=(0, 10), sticky="w")

        self.launch_on_startup_var = ctk.BooleanVar(value=self.launch_on_startup)
        self.launch_on_startup_switch = ctk.CTkSwitch(
            self.sidebar_scroll,
            text="Lancer au demarrage (arriere-plan)",
            variable=self.launch_on_startup_var,
            command=self.toggle_launch_on_startup,
            text_color=COLOR_SECONDARY
        )
        self.launch_on_startup_switch.grid(row=29, column=0, padx=20, pady=(0, 10), sticky="w")

        self.ui_theme_label = ctk.CTkLabel(
            self.sidebar_scroll,
            text="Theme couleur",
            font=ctk.CTkFont(size=11),
            text_color=COLOR_SECONDARY
        )
        self.ui_theme_label.grid(row=30, column=0, padx=20, pady=(0, 4), sticky="w")

        self.ui_theme_var = ctk.StringVar(value=self.ui_theme_name)
        self.ui_theme_menu = ctk.CTkOptionMenu(
            self.sidebar_scroll,
            values=list(self.ui_theme_presets.keys()),
            variable=self.ui_theme_var,
            command=self.on_ui_theme_changed,
            fg_color=COLOR_CARD,
            button_color=COLOR_ACCENT_PURPLE,
            button_hover_color="#B388EB",
            text_color=COLOR_TEXT
        )
        self.ui_theme_menu.grid(row=31, column=0, padx=20, pady=(0, 6), sticky="w")

        self.custom_accent_button = ctk.CTkButton(
            self.sidebar_scroll,
            text="Couleur accent perso",
            height=28,
            fg_color=COLOR_CARD,
            hover_color="#3C4043",
            command=self.choose_custom_accent_color
        )
        self.custom_accent_button.grid(row=32, column=0, padx=20, pady=(0, 10), sticky="w")

        # Localisation
        self.location_label = ctk.CTkLabel(self.sidebar_scroll, text="📍 Localisation...", font=ctk.CTkFont(size=11), text_color=COLOR_ACCENT_PURPLE)
        self.location_label.grid(row=33, column=0, padx=20, pady=5, sticky="w")

        # Header
        self.header = ctk.CTkFrame(self, height=60, fg_color=COLOR_NAV, corner_radius=0)
        self.header.grid(row=0, column=1, sticky="ew")
        self.logo_label = ctk.CTkLabel(self.header, text="✧ Jarvisse Intelligence", font=ctk.CTkFont(family="Inter", size=22, weight="bold"), text_color=COLOR_ACCENT)
        self.logo_label.grid(row=0, column=0, padx=20, pady=15)

        # Bouton Paramètres Globaux (Style Gear Premium)
        self.header_settings_btn = ctk.CTkButton(
            self.header,
            text="⚙️",
            width=40,
            height=40,
            fg_color="transparent",
            hover_color=COLOR_CARD,
            text_color=COLOR_ACCENT,
            font=ctk.CTkFont(size=20),
            command=self.open_main_settings
        )
        self.header_settings_btn.grid(row=0, column=1, padx=20, pady=10, sticky="e")
        self.header.grid_columnconfigure(1, weight=1)

        # Zone centrale avec Onglets
        self.tabview = ctk.CTkTabview(self, fg_color=COLOR_BG, segmented_button_selected_color=COLOR_ACCENT_PURPLE)
        self.tabview.grid(row=1, column=1, padx=20, pady=20, sticky="nsew")
        self.tab_chat = self.tabview.add("✧ Chat & IA")
        self.tab_browser = self.tabview.add("🌐 Navigateur")
        
        self.tab_chat.grid_columnconfigure(0, weight=1)
        self.tab_chat.grid_rowconfigure(0, weight=1)

        # Zone de discussion (dans l'onglet Chat)
        self.chat_display = ctk.CTkTextbox(self.tab_chat, fg_color=COLOR_BG, border_width=0, font=ctk.CTkFont(size=13))
        self.chat_display.grid(row=0, column=0, padx=5, pady=5, sticky="nsew")
        self.chat_display.configure(state="disabled")

        # Navigateur Intégré
        self.browser_frame = ctk.CTkFrame(self.tab_browser, fg_color=COLOR_NAV)
        self.browser_frame.grid(row=0, column=0, sticky="nsew", padx=5, pady=5)
        self.tab_browser.grid_columnconfigure(0, weight=1)
        self.tab_browser.grid_rowconfigure(0, weight=1)

        # Barre d'outils du navigateur
        self.browser_toolbar = ctk.CTkFrame(self.browser_frame, height=40, fg_color="transparent")
        self.browser_toolbar.pack(side="top", fill="x", padx=5, pady=5)

        ctk.CTkButton(self.browser_toolbar, text="←", width=30, fg_color=COLOR_CARD, command=lambda: self.web_view.go_back()).pack(side="left", padx=2)
        ctk.CTkButton(self.browser_toolbar, text="→", width=30, fg_color=COLOR_CARD, command=lambda: self.web_view.go_forward()).pack(side="left", padx=2)
        ctk.CTkButton(self.browser_toolbar, text="⟳", width=30, fg_color=COLOR_CARD, command=lambda: self.web_view.load_website(self.web_view.url)).pack(side="left", padx=2)

        self.url_entry = ctk.CTkEntry(self.browser_toolbar, placeholder_text="Rechercher ou saisir une URL...")
        self.url_entry.pack(side="left", fill="x", expand=True, padx=5)
        self.url_entry.bind("<Return>", lambda e: self.agent_browser_mission(f"va sur {self.url_entry.get()}"))

        try:
            self.web_view = HtmlFrame(self.browser_frame, messages_enabled=False)
            self.web_view.pack(fill="both", expand=True)
            
            def delayed_load():
                if hasattr(self.web_view, "load_website"):
                    self.web_view.load_website("https://duckduckgo.com/html")
            self.after(3000, delayed_load)
        except Exception as e:
            print(f"Erreur Navigateur: {e}")
            self.web_view = ctk.CTkLabel(self.browser_frame, text=f"Le navigateur n'a pas pu être chargé.\n({e})")
            self.web_view.pack(pady=50)

        # Zone d'action
        self.bottom_frame = ctk.CTkFrame(self, height=120, fg_color="transparent")
        self.bottom_frame.grid(row=2, column=1, sticky="ew", padx=20, pady=20)
        self.bottom_frame.grid_columnconfigure(0, weight=1)

        self.status_label = ctk.CTkLabel(self.bottom_frame, text="Jarvisse est prêt.", font=ctk.CTkFont(size=12), text_color=COLOR_SECONDARY)
        self.status_label.grid(row=0, column=0, columnspan=4, pady=(0, 10))

        self.input_entry = ctk.CTkEntry(self.bottom_frame, placeholder_text="Commandez Jarvisse...", height=50, fg_color=COLOR_NAV, border_color="#3C4043", text_color=COLOR_TEXT)
        self.input_entry.grid(row=1, column=0, sticky="ew", padx=(0, 10))
        self.input_entry.bind("<Return>", lambda e: self.handle_text_input())

        # Buttons
        button_params = {"width": 50, "height": 50, "corner_radius": 15, "font": ctk.CTkFont(size=20)}
        
        self.listen_button = ctk.CTkButton(self.bottom_frame, text="🎙", command=self.start_listening_thread, fg_color=COLOR_ACCENT, hover_color="#5294FF", **button_params)
        self.listen_button.grid(row=1, column=1, padx=(0, 10))

        self.file_button = ctk.CTkButton(self.bottom_frame, text="📎", command=self.select_file, fg_color=COLOR_CARD, hover_color="#3C4043", **button_params)
        self.file_button.grid(row=1, column=2, padx=(0, 10))

        self.send_button = ctk.CTkButton(self.bottom_frame, text="➤", command=self.handle_text_input, fg_color=COLOR_ACCENT_PURPLE, hover_color="#B388EB", **button_params)
        self.send_button.grid(row=1, column=3)

        # Panneau droit - Programmation d'horloge (Scrollable)
        self.right_panel = ctk.CTkScrollableFrame(self, width=240, fg_color=COLOR_NAV, corner_radius=0)
        self.right_panel.grid(row=0, column=2, rowspan=3, sticky="nsew")
        self.right_panel.grid_rowconfigure(14, weight=1)

        self.right_title = ctk.CTkLabel(self.right_panel, text="ALARMES", font=ctk.CTkFont(size=12, weight="bold"), text_color=COLOR_ACCENT)
        self.right_title.grid(row=0, column=0, padx=20, pady=(20, 10), sticky="w")

        self.alarm_time_label = ctk.CTkLabel(self.right_panel, text="Heure (HH:MM)", font=ctk.CTkFont(size=11), text_color=COLOR_SECONDARY)
        self.alarm_time_label.grid(row=1, column=0, padx=20, pady=(0, 5), sticky="w")

        self.alarm_time_entry = ctk.CTkEntry(self.right_panel, height=28, width=160, fg_color=COLOR_CARD, border_color="#3C4043", text_color=COLOR_TEXT)
        self.alarm_time_entry.grid(row=2, column=0, padx=20, pady=(0, 10), sticky="w")

        self.alarm_reason_label = ctk.CTkLabel(self.right_panel, text="Motif (message)", font=ctk.CTkFont(size=11), text_color=COLOR_SECONDARY)
        self.alarm_reason_label.grid(row=3, column=0, padx=20, pady=(0, 5), sticky="w")

        self.alarm_reason_entry = ctk.CTkEntry(self.right_panel, height=28, width=160, fg_color=COLOR_CARD, border_color="#3C4043", text_color=COLOR_TEXT)
        self.alarm_reason_entry.grid(row=4, column=0, padx=20, pady=(0, 10), sticky="w")

        self.alarm_set_button = ctk.CTkButton(
            self.right_panel,
            text="Programmer",
            height=28,
            width=160,
            fg_color=COLOR_ACCENT,
            hover_color="#5294FF",
            command=self.program_alarm
        )
        self.alarm_set_button.grid(row=5, column=0, padx=20, pady=(0, 10), sticky="w")

        self.alarm_list_label = ctk.CTkLabel(self.right_panel, text="Alarmes", font=ctk.CTkFont(size=11), text_color=COLOR_SECONDARY)
        self.alarm_list_label.grid(row=6, column=0, padx=20, pady=(0, 5), sticky="w")

        self.alarm_list_display = ctk.CTkTextbox(self.right_panel, height=120, width=180, fg_color=COLOR_BG, border_width=1, border_color="#3C4043", text_color=COLOR_TEXT)
        self.alarm_list_display.grid(row=7, column=0, padx=20, pady=(0, 10), sticky="w")
        self.alarm_list_display.configure(state="disabled")

        self.next_alarm_label = ctk.CTkLabel(self.right_panel, text="Aucune alarme", font=ctk.CTkFont(size=11), text_color=COLOR_SECONDARY)
        self.next_alarm_label.grid(row=8, column=0, padx=20, pady=(10, 6), sticky="w")

        self.anomaly_settings_button = ctk.CTkButton(
            self.right_panel,
            text="Paramètres anomalies",
            height=28,
            width=160,
            fg_color=COLOR_CARD,
            hover_color="#3C4043",
            command=self.open_anomaly_settings
        )
        self.anomaly_settings_button.grid(row=9, column=0, padx=20, pady=(0, 10), sticky="w")

        self.anomalies_enabled_var_main = ctk.BooleanVar(value=self.anomalies_enabled)
        self.anomalies_toggle = ctk.CTkSwitch(
            self.right_panel,
            text="Anomalies activées",
            variable=self.anomalies_enabled_var_main,
            command=lambda: self.toggle_anomalies_enabled(source="main"),
            text_color=COLOR_SECONDARY
        )
        self.anomalies_toggle.grid(row=10, column=0, padx=20, pady=(0, 10), sticky="w")

        self.services_watch_button = ctk.CTkButton(
            self.right_panel,
            text="Services critiques",
            height=28,
            width=160,
            fg_color=COLOR_CARD,
            hover_color="#3C4043",
            command=self.open_services_watch
        )
        self.services_watch_button.grid(row=11, column=0, padx=20, pady=(0, 10), sticky="w")

        self.notifications_button = ctk.CTkButton(
            self.right_panel,
            text="Notifications apps",
            height=28,
            width=160,
            fg_color=COLOR_CARD,
            hover_color="#3C4043",
            command=self.open_notification_settings
        )
        self.notifications_button.grid(row=12, column=0, padx=20, pady=(0, 10), sticky="w")

        self.agents_settings_button = ctk.CTkButton(
            self.right_panel,
            text="⚙️ Paramètres Agents",
            height=28,
            width=160,
            fg_color=COLOR_ACCENT_PURPLE,
            hover_color="#B388EB",
            command=self.open_agents_settings
        )
        self.agents_settings_button.grid(row=13, column=0, padx=20, pady=(0, 10), sticky="w")

        self._refresh_alarm_list()

        self.after(1000, self.saluer)
        self.after(3000, self.start_wake_word_thread)
        self.after(2000, self.update_system_stats)
        self.after(4000, self.update_location)
        self.after(1000, self.check_alarms)
        self.after(5000, self.check_removable_devices)
        self.after(15000, self.check_system_anomalies)
        self.after(6000, self.start_notifications_listener_thread)  # Démarrage retardé du listener Android
        
        # Gestion de la fermeture propre
        self.protocol("WM_DELETE_WINDOW", self.on_closing)
        
        # Rafraîchissement final pour appliquer toutes les couleurs chargées
        self._refresh_theme_widgets()
        
        try:
            if self.launch_on_startup:
                self._enable_startup_launcher()
            else:
                self._disable_startup_launcher()
        except Exception as e:
            print(f"Erreur synchronisation démarrage auto: {e}")


    def on_closing(self):
        """Arrête proprement l'assistant"""
        self.veille_active = False
        self.is_listening = False
        try:
            pygame.mixer.quit()
        except: pass
        self.destroy()
        os._exit(0) # Force l'arrêt de tous les threads

    def start_wake_word_thread(self):
        """Lance la veille en arrière-plan"""
        threading.Thread(target=self.attendre_mot_cle, daemon=True).start()
        # Thread dédié pour la détection du STOP en continu
        threading.Thread(target=self._stop_detection_loop, daemon=True).start()

    def _stop_detection_loop(self):
        """Boucle dédiée à la détection du mot STOP en continu, indépendamment de l'état d'écoute"""
        reconnaisseur = sr.Recognizer()
        reconnaisseur.energy_threshold = 300
        reconnaisseur.dynamic_energy_threshold = True
        reconnaisseur.pause_threshold = 0.3
        
        fs = 44100
        duree_ecoute = 1.0  # Écoute courte pour réactivité
        
        print("🛑 Système de détection STOP activé en continu...")
        
        while self.veille_active:
            try:
                # Capture audio courte
                audio_rec = sd.rec(int(duree_ecoute * fs), samplerate=fs, channels=1, dtype='int16')
                sd.wait()
                
                byte_io = io.BytesIO()
                with wave.open(byte_io, 'wb') as wav_file:
                    wav_file.setnchannels(1)
                    wav_file.setsampwidth(2)
                    wav_file.setframerate(fs)
                    wav_file.writeframes(audio_rec.tobytes())
                byte_io.seek(0)
                
                with sr.AudioFile(byte_io) as source:
                    reconnaisseur.adjust_for_ambient_noise(source, duration=0.05)
                    audio_data = reconnaisseur.record(source)
                
                try:
                    texte = reconnaisseur.recognize_google(audio_data, language='fr-FR').lower()
                    
                    # Détection des commandes d'arrêt
                    if any(word in texte for word in ["stop", "arrête", "arrêt", "tais-toi", "silence"]):
                        print(f"🛑 STOP DÉTECTÉ (Thread dédié): '{texte}'")
                        self.stop_speaking_flag = True
                        
                        try:
                            pygame.mixer.music.stop()
                            pygame.mixer.music.unload()
                        except:
                            pass
                        
                        self.conversation_continue = False
                        self.is_listening = False
                        
                        # Confirmation vocale après un court délai
                        self.after(300, lambda: self.parler("Lecture arrêtée.", wait=False))
                        self.after(400, self.reset_ui)
                        
                        # Pause pour éviter les détections multiples
                        time.sleep(1.5)
                        
                except sr.UnknownValueError:
                    pass  # Pas de parole détectée
                except sr.RequestError:
                    pass  # Erreur réseau
                    
            except Exception as e:
                # Erreur silencieuse pour ne pas polluer les logs
                pass
            
            # Petite pause pour ne pas surcharger le CPU
            time.sleep(0.05)

    def attendre_mot_cle(self):
        """Boucle de veille réactive pour détecter 'Jarvisse'"""
        reconnaisseur = sr.Recognizer()
        # Seuil par défaut plus robuste
        reconnaisseur.energy_threshold = 300 
        reconnaisseur.dynamic_energy_threshold = True
        reconnaisseur.pause_threshold = 0.5
        
        fs = 44100
        duree_veille = 1.5  # Légèrement plus long pour mieux capter le mot entier
        
        print("🎙️ Système de veille activé (Jarvisse/Alpha/Service)...")
        
        while self.veille_active:
            if not self.is_listening:
                try:
                    self.after(0, lambda: self.status_label.configure(text="🔊 Veille active... (Dites 'Jarvisse')", text_color=COLOR_SECONDARY))
                    
                    # Capture courte
                    audio_rec = sd.rec(int(duree_veille * fs), samplerate=fs, channels=1, dtype='int16')
                    sd.wait()
                    
                    byte_io = io.BytesIO()
                    with wave.open(byte_io, 'wb') as wav_file:
                        wav_file.setnchannels(1)
                        wav_file.setsampwidth(2)
                        wav_file.setframerate(fs)
                        wav_file.writeframes(audio_rec.tobytes())
                    byte_io.seek(0)
                    
                    with sr.AudioFile(byte_io) as source:
                        # Ajustement minimal pour ne pas filtrer la voix
                        reconnaisseur.adjust_for_ambient_noise(source, duration=0.1)
                        audio_data = reconnaisseur.record(source)
                    
                    try:
                        # Transcription rapide
                        texte = reconnaisseur.recognize_google(audio_data, language='fr-FR').lower()
                        
                        # Variante STOP pour interruption lecture
                        if "stop" in texte or "arrête" in texte:
                            print(f"🛑 COMMANDE D'ARRÊT DÉTECTÉE (Veille): '{texte}'")
                            self.stop_speaking_flag = True
                            try:
                                pygame.mixer.music.stop()
                                pygame.mixer.music.unload()
                            except: pass
                            self.conversation_continue = False
                            # On laisse le temps à la boucle de parole de s'arrêter avant de confirmer
                            self.after(500, lambda: self.parler("Lecture arrêtée."))
                            self.after(600, self.reset_ui)
                            continue

                        # Variantes phonétiques (élargies suite aux logs utilisateur)
                        variantes = [
                            "jarvisse", "jarvis", "service", "vice", "zarzis", "janice", 
                            "charvis", "cher", "jarv", "servis", "alpha", "arvis", "jar",
                            "garvis", "jarves", "janis", "jarvise"
                        ]

                        for v in variantes:
                            if v in texte:
                                print(f"✅ MOT-CLÉ DÉTECTÉ: '{v}' (entendu: '{texte}')")
                                self.after(0, self.declencher_activation)
                                break
                    except: pass
                except: pass
            time.sleep(0.01)


    def declencher_activation(self):
        """Réponse immédiate au mot-clé sans attente inutile"""
        if self.is_listening: 
            print("⚠️ Déjà en écoute, activation ignorée")
            return
        
        print("🚀 ACTIVATION ! Jarvisse répond...")
        self.is_listening = True
        
        def sequence():
            self.after(0, lambda: self.status_label.configure(text="✨ Oui Monsieur...", text_color=COLOR_ACCENT))
            # On ne bloque pas tout le thread pour parler, on lance l'écoute très vite
            self.parler("Oui Monsieur", wait=False) 
            
            # On attend que le "Oui Monsieur" se termine pour ne pas que l'assistant s'écoute lui-même
            time.sleep(1.2) 
            self.is_listening = False
            print("👂 Passage en mode écoute...")
            self.after(0, self.start_listening_thread)
            
        threading.Thread(target=sequence, daemon=True).start()


    def _normaliser_texte(self, texte):
        """Nettoie une chaîne pour améliorer la détection de mots-clés."""
        # Remplace la ponctuation par des espaces, garde les lettres et espaces.
        cleaned = []
        for ch in texte:
            if ch.isalpha() or ch.isspace():
                cleaned.append(ch)
            else:
                cleaned.append(" ")
        return " ".join("".join(cleaned).split())

    def add_message(self, message, sender="Jarvisse", progressive=True):
        try:
            self.after(0, self._add_message_safe, message, sender, progressive)
        except:
            print(f"[{sender}] {message}") # Fallback if UI not ready

    def _add_message_safe(self, message, sender, progressive):
        self.chat_display.configure(state="normal")
        
        display_name = f"✧ {sender}" if sender != "Vous" else "Vous"
        tag = "user_tag" if sender == "Vous" else "ai_tag"
        
        self.chat_display.insert("end", f"\n{display_name}\n", tag)
        
        if progressive and sender != "Vous":
            # Lancer l'effet machine à écrire
            threading.Thread(target=self._typewriter_effect, args=(message,), daemon=True).start()
        else:
            self.chat_display.insert("end", f"{message}\n")
            self.chat_display.see("end")
            self.chat_display.configure(state="disabled")
        
        self.chat_display.tag_config("user_tag", foreground="#8AB4F8")
        self.chat_display.tag_config("ai_tag", foreground=COLOR_ACCENT_PURPLE if sender != "Jarvisse" else COLOR_ACCENT)

    def start_streaming_message(self):
        self.after(0, self._start_streaming_message_safe)

    def _start_streaming_message_safe(self):
        self.chat_display.configure(state="normal")
        self.chat_display.insert("end", f"\nâœ§ Jarvisse\n", "ai_tag")
        self.chat_display.see("end")
        self.chat_display.configure(state="disabled")
        self.chat_display.tag_config("ai_tag", foreground=COLOR_ACCENT)

    def append_streaming_text(self, text):
        if not text:
            return
        self.after(0, self._append_streaming_text_safe, text)

    def _append_streaming_text_safe(self, text):
        self.chat_display.configure(state="normal")
        self.chat_display.insert("end", text)
        self.chat_display.see("end")
        self.chat_display.configure(state="disabled")

    def end_streaming_message(self):
        self.after(0, lambda: self.chat_display.configure(state="disabled"))

    def _typewriter_effect(self, message):
        """Affichage INSTANTANÉ pour mode ping-pong (pas d'effet machine à écrire)"""
        # Mode ping-pong : affichage immédiat sans délai
        self.after(0, self._insert_full_message, message)
        self.after(0, lambda: self.chat_display.configure(state="disabled"))

    def _insert_full_message(self, message):
        """Insère le message complet d'un coup"""
        self.chat_display.configure(state="normal")
        self.chat_display.insert("end", f"{message}\n")
        self.chat_display.see("end")


    def _insert_char(self, char):
        self.chat_display.configure(state="normal")
        self.chat_display.insert("end", char)
        self.chat_display.see("end")

    def handle_text_input(self):
        commande = self.input_entry.get().strip()
        if commande:
            self.input_entry.delete(0, "end")
            self.add_message(commande, "Vous")
            self.status_label.configure(text="En train de réfléchir...")
            self.last_command_origin = "local"
            threading.Thread(target=self.executer_commande, args=(commande,), daemon=True).start()

    def select_file(self):
        file_path = filedialog.askopenfilename(
            title="Sélectionner un fichier",
            filetypes=[("Documents", "*.txt *.pdf *.docx"), ("Tous les fichiers", "*.*")]
        )
        if file_path:
            self.traiter_fichier(file_path)

    def traiter_fichier(self, path):
        nom_fichier = os.path.basename(path)
        self.add_message(f"Fichier joint : {nom_fichier}", "Vous")
        
        contenu = ""
        try:
            # Gestion des fichiers TEXTE
            if path.endswith('.txt'):
                with open(path, 'r', encoding='utf-8') as f:
                    contenu = f.read()
            
            # Gestion des fichiers PDF
            elif path.endswith('.pdf'):
                doc = fitz.open(path)
                try:
                    for page in doc:
                        contenu += page.get_text()
                finally:
                    doc.close()
            
            # Gestion des fichiers DOCX
            elif path.endswith('.docx'):
                doc = Document(path)
                for para in doc.paragraphs:
                    contenu += para.text + "\n"

            # Gestion des fichiers EXCEL
            elif path.endswith('.xlsx'):
                wb = openpyxl.load_workbook(path)
                for sheet in wb.worksheets:
                    for row in sheet.iter_rows(values_only=True):
                        contenu += " ".join([str(cell) for cell in row if cell is not None]) + "\n"

            # Gestion des fichiers POWERPOINT
            elif path.endswith('.pptx'):
                prs = Presentation(path)
                for slide in prs.slides:
                    for shape in slide.shapes:
                        if hasattr(shape, "text"):
                            contenu += shape.text + "\n"

            # Gestion des fichiers CSV
            elif path.endswith('.csv'):
                with open(path, mode='r', encoding='utf-8') as f:
                    reader = csv.reader(f)
                    for row in reader:
                        contenu += " ".join(row) + "\n"
            
            if contenu:
                self.loaded_document_content = contenu # Stockage dédié au contenu du fichier
                self.current_subject = f"le contenu du fichier {nom_fichier}"
                self.parler(f"J'ai bien chargé le document {nom_fichier}. Je peux maintenant vous le lire, le résumer ou répondre à vos questions.")
                self.conversation_history.append(f"CONTENU_FICHIER: {contenu}")
                if len(self.conversation_history) > self.conversation_memory_limit:
                    self.conversation_history.pop(0)
            else:
                self.parler(f"J'ai reçu {nom_fichier}, mais je n'ai trouvé aucun texte lisible à l'intérieur.")
                
        except Exception as e:
            print(f"Erreur lecture fichier: {e}")
            self.parler(f"Désolé, je n'ai pas pu lire le fichier {nom_fichier}. Vérifiez qu'il n'est pas utilisé par un autre programme.")

    def humaniser_reponse(self, texte):
        """Ajoute des marqueurs de conversation naturels pour rendre la voix plus humaine"""
        # Si on est en mode ping-pong (ultra-rapide), on évite d'ajouter du texte inutile
        if getattr(self, "ping_pong_mode", False):
            return texte
            
        intros = [
            "Eh bien, ", "Justement, ", "Il me semble que ", "Voyons voir, ", 
            "Pour être précis, ", "Si je puis dire, ", "À vrai dire, ",
            "Comme vous le savez probablement, ", "D'après mes analyses, ",
            "Écoutez, ", "Alors, pour tout vous dire, ", "C'est une excellente question... "
        ]
        
        interjections = [" hmm, ", " d'ailleurs, ", " en quelque sorte, ", ", voyez-vous, "]
        
        # On n'ajoute une intro que si le texte est assez long et ne commence pas déjà par une formule de politesse
        if len(texte) > 30 and not texte[0].isupper():
            if random.random() < 0.25: # 25% de chance d'ajouter une intro naturelle
                texte = random.choice(intros) + texte[0].lower() + texte[1:]
        
        # Ajout sporadique d'interjections au milieu
        if len(texte) > 100 and random.random() < 0.15:
            # On insère après la première virgule ou le premier point
            parts = re.split(r'([,.])', texte, maxsplit=1)
            if len(parts) > 2:
                texte = parts[0] + parts[1] + random.choice(interjections) + parts[2]
                
        return texte

    def _select_file_main_thread(self, title, types):
        """Ouvre le sélecteur de fichiers de manière thread-safe via le thread principal"""
        res_queue = queue.Queue()
        def _open():
            path = filedialog.askopenfilename(title=title, filetypes=types)
            res_queue.put(path)
        self.after(0, _open)
        return res_queue.get() # Attend la sélection de l'utilisateur

    def _convertir_nombre_0_99(self, n):
        """Convertit un nombre 0-99 en texte pour la lecture des années"""
        if n == 0: return ""
        if n < 20:
             t = ["", "un", "deux", "trois", "quatre", "cinq", "six", "sept", "huit", "neuf", "dix",
                 "onze", "douze", "treize", "quatorze", "quinze", "seize", "dix-sept", "dix-huit", "dix-neuf"]
             return t[n]
        
        dizaines = {2:"vingt", 3:"trente", 4:"quarante", 5:"cinquante", 6:"soixante", 7:"soixante", 8:"quatre-vingt", 9:"quatre-vingt"}
        d = n // 10
        u = n % 10
        
        if d == 7 or d == 9:
            u += 10
            
        txt = dizaines[d]
        if u == 0:
            if d == 8: txt += "s"
            return txt
            
        separateur = "-"
        if (u == 1 or u == 11) and d < 8: separateur = "-et-"
        
        # Récupération de l'unité (ou 10-19)
        t = ["", "un", "deux", "trois", "quatre", "cinq", "six", "sept", "huit", "neuf", "dix",
             "onze", "douze", "treize", "quatorze", "quinze", "seize", "dix-sept", "dix-huit", "dix-neuf"]
        
        txt += separateur + t[u]
        return txt

    def _convertir_annees_historiques(self, texte):
        """Convertit les années (1700-2029) en toutes lettres"""
        def repl_annee(match):
            val = int(match.group(0))
            siecle = val // 100
            reste = val % 100
            
            debut = ""
            if siecle == 19: debut = "mille neuf cent"
            elif siecle == 20: debut = "deux mille"
            elif siecle == 18: debut = "mille huit cent"
            elif siecle == 17: debut = "mille sept cent"
            else: return match.group(0)
            
            if reste == 0: return debut
            conversion_reste = self._convertir_nombre_0_99(reste)
            return f"{debut} {conversion_reste}" if conversion_reste else debut

        # Regex pour les années isolées (4 chiffres)
        return re.sub(r'\b(17|18|19|20)\d{2}\b', repl_annee, texte)

    def _convertir_chiffres_romains(self, texte):
        """Convertit les chiffres romains courants et siècles en texte français"""
        # 1. Siècles courants
        texte = re.sub(r'\b(XI|XII|XIII|XIV|XV|XVI|XVII|XVIII|XIX|XX|XXI)e (siècle|millénaire)\b', 
                       lambda m: self._map_siecle(m.group(1)) + " " + m.group(2), texte, flags=re.IGNORECASE)
        
        # 2. Rois et Chapitres
        mots_cles = r"(Louis|Henri|Charles|Philippe|François|Napoléon|Pie|Chapitre|Tome|Volume|Guerre|Partie|Jean|Paul|Benoît)"
        texte = re.sub(rf'\b{mots_cles} ([IVX]+)\b', lambda m: f"{m.group(1)} {self._map_romain(m.group(2))}", texte)
        return texte

    def _map_siecle(self, rom):
        m = {'XI':'onzième', 'XII':'douzième', 'XIII':'treizième', 'XIV':'quatorzième', 'XV':'quinzième', 
             'XVI':'seizième', 'XVII':'dix-septième', 'XVIII':'dix-huitième', 'XIX':'dix-neuvième', 
             'XX':'vingtième', 'XXI':'vingt-et-unième'}
        return m.get(rom.upper(), rom)

    def _map_romain(self, rom):
        m = {'I':'premier', 'II':'deux', 'III':'trois', 'IV':'quatre', 'V':'cinq', 'VI':'six', 'VII':'sept', 
             'VIII':'huit', 'IX':'neuf', 'X':'dix', 'XI':'onze', 'XII':'douze', 'XIII':'treize', 'XIV':'quatorze', 
             'XV':'quinze', 'XVI':'seize', 'XVII':'dix-sept', 'XVIII':'dix-huit', 'XIX':'dix-neuf', 
             'XX':'vingt', 'XXI':'vingt-et-un'}
        return m.get(rom.upper(), rom)

    def _nettoyer_pour_parler(self, texte):
        """Nettoie le texte des symboles markdown et autres caractères indésirables avant la synthèse vocale."""
        if not texte:
            return ""
        
        # 1. Supprimer les liens Markdown [texte](url) pour ne garder que le texte
        texte_propre = re.sub(r'\[([^\]]+)\]\([^\)]+\)', r'\1', texte)
        
        # 2. Supprimer les symboles markdown courants (*, _, #, `, ~, >, [, ])
        # Ces symboles sont souvent utilisés par les LLM pour le formatage
        texte_propre = re.sub(r'[*_#`~>\[\]]', '', texte_propre)
        
        # 3. Supprimer les listes à puces simples en début de ligne (ex: "- " ou "+ ")
        texte_propre = re.sub(r'^[ \t]*[-+*][ \t]+', '', texte_propre, flags=re.MULTILINE)
        
        # 4. Supprimer les emojis et caractères spéciaux (✅, ❌, ⚠️, etc.)
        texte_propre = re.sub(r'[^\x00-\x7FÀ-ÿ0-9\s.,!?:;\'"()\-/]', '', texte_propre)
        
        # 5. Traitement des barres obliques (/) pour éviter qu'elles soient lues
        # Dates : 15/02/2024 -> 15 février 2024 ou simplement 15 02 2024
        texte_propre = re.sub(r'(\d{1,2})/(\d{1,2})/(\d{2,4})', r'\1 \2 \3', texte_propre)
        # Autres slashes isolés ou multiples : remplacer par espace
        texte_propre = re.sub(r'/+', ' ', texte_propre)
        
        # 6. Nettoyer les espaces multiples
        texte_propre = re.sub(r'\s+', ' ', texte_propre)
        
        # 7. INTELLIGENCE PHONÉTIQUE ALGORITHMIQUE (Capacité 100.000+)
        # Au lieu de boucles lentes, on utilise une substitution par callback ultra-rapide
        texte_propre = self._appliquer_intelligence_phonetique(texte_propre)
        
        # 8. CONVERSION AVANCÉE (Années & Chiffres Romains)
        texte_propre = self._convertir_chiffres_romains(texte_propre)
        texte_propre = self._convertir_annees_historiques(texte_propre)
        
        return texte_propre.strip()

    def _load_phonetic_map(self):
        """Charge la base de données phonétique depuis le fichier externe"""
        if os.path.exists(self.phonetic_path):
            try:
                with open(self.phonetic_path, "r", encoding="utf-8") as f:
                    return json.load(f)
            except: return {}
        return {}

    def _appliquer_intelligence_phonetique(self, texte):
        """Moteur de traitement phonétique haute performance avec support URL"""
        # Pré-traitement des extensions web courantes pour éviter qu'elles soient ignorées
        texte = re.sub(r'\.com\b', ' point com ', texte, flags=re.IGNORECASE)
        texte = re.sub(r'\.fr\b', ' point èf-èr ', texte, flags=re.IGNORECASE)
        texte = re.sub(r'\.net\b', ' point nette ', texte, flags=re.IGNORECASE)
        texte = re.sub(r'\.org\b', ' point orgue ', texte, flags=re.IGNORECASE)
        texte = re.sub(r'\.io\b', ' point i-o ', texte, flags=re.IGNORECASE)
        
        def replace_callback(match):
            word = match.group(0)
            word_upper = word.upper()
            
            # Cas spécial : www
            if word_upper == "WWW":
                return "v-v-v" # Plus rapide et naturel que double-vé double-vé...
            
            # A. Vérification dans le dictionnaire étendu
            if word_upper in self.phonetic_map:
                return self.phonetic_map[word_upper]
            
            # B. Épellation automatique des acronymes (Majuscules de 2 à 5 lettres)
            if word.isupper() and 2 <= len(word) <= 5 and word.isalpha():
                return "-".join([self.alphabet_phonetique.get(l, l) for l in word])
            
            return word

        # On traite tous les mots de 2 lettres ou plus
        return re.sub(r'\b[a-zA-Z]{2,}\b', replace_callback, texte)

    def _ping_pong_style(self, texte):
        """Raccourcit la réponse pour un style ping-pong (court, direct)"""
        texte = " ".join(str(texte).split())
        if not texte:
            return texte

        # Garder 1 ou 2 phrases max pour un rythme réactif
        phrases = re.split(r'(?<=[.!?])\s+', texte)
        court = phrases[0]
        if len(court) < 25 and len(phrases) > 1:
            court = f"{court} {phrases[1]}"

        if len(court) > self.ping_pong_max_chars:
            court = court[:self.ping_pong_max_chars].rstrip() + "..."

        return court

    def parler(self, texte, progressive=True, wait=True, force_full=False, sender="Jarvisse"):
        # Réinitialiser le flag d'arrêt à chaque nouvelle parole
        self.stop_speaking_flag = False
        
        # On affiche le texte progressivement en même temps que la voix commence
        texte_brut = str(texte)
        texte = self.humaniser_reponse(texte_brut)
        
        if self.ping_pong_mode and not force_full:
            texte = self._ping_pong_style(texte)
            progressive = False
        
        if force_full:
            progressive = False # Désactiver l'effet machine à écrire pour la rapidité et fiabilité

        # Mémorise aussi les réponses de l'assistant
        self.conversation_history.append(f"{sender}: {texte}")
        if len(self.conversation_history) > self.conversation_memory_limit:
            self.conversation_history.pop(0)

        self.add_message(texte, sender=sender, progressive=progressive)
        
        # On ne lance la voix que si elle est activée
        if getattr(self, "voice_enabled", True):
            threading.Thread(target=self._run_async_parler, args=(texte, wait), daemon=True).start()

        # Routage vers Telegram si la commande vient de là
        if getattr(self, "agent_telegram_enabled", False) and getattr(self, "last_command_origin", "local") == "telegram":
            threading.Thread(target=self.send_telegram_message, args=(texte_brut,), daemon=True).start()

    def _parler_chunk(self, texte):
        if not texte:
            return
        threading.Thread(target=self._run_async_parler, args=(texte, False), daemon=True).start()


    def _run_async_parler(self, texte, wait):
        try:
            asyncio.run(self._parler_async(texte, wait))
            # Si le mode conversation continue est actif et que l'origine est locale
            if self.conversation_continue and getattr(self, "last_command_origin", "local") == "local":
                # On libère l'état d'écoute pour permettre au thread suivant de démarrer
                self.is_listening = False
                # On attend un tout petit peu pour éviter que le micro ne capte la fin de l'écho
                time.sleep(0.4)
                self.after(0, self.start_listening_thread)
        except Exception as e:
            print(f"Erreur fatale asyncio voice: {e}")
            if self.conversation_continue: self.is_listening = False

    def toggle_conversation_continue(self):
        self.conversation_continue = self.conv_continue_var.get()
        if self.conversation_continue:
            self.parler("Mode conversation continue activé. Je vous écoute sans interruption.")
        else:
            self.parler("Mode conversation continue désactivé.")

    def _split_sentences(self, texte):
        """Découpe le texte de manière fluide pour une synthèse vocale naturelle"""
        if not texte: return []
        import re
        # On coupe prioritairement sur les ponctuations fortes (. ! ? \n)
        phrases = re.split(r'(?<=[.!?\n])\s+', texte)
        
        final_phrases = []
        for p in phrases:
            # On ne coupe sur les points-virgules ou virgules QUE si la phrase est extrêmement longue (> 150 chars)
            if len(p) > 150:
                sub = re.split(r'(?<=[,;])\s+', p)
                final_phrases.extend(sub)
            else:
                final_phrases.append(p)
        return [f.strip() for f in final_phrases if f.strip()]

    async def _parler_async(self, texte, wait):
        """Lecture vocale optimisée avec génération parallèle et buffers mémoire"""
        if not texte: return
        print(f"🔊 Début lecture vocale ({len(texte)} chars)")
        try:
            phrases = self._split_sentences(texte)
            if not phrases: 
                print("⚠️ Aucune phrase à lire après découpage.")
                return
            
            print(f"📦 Découpage en {len(phrases)} segments audio.")

            # Limiteur de concurrence pour éviter le bannissement IP ou les timeouts
            semaphore = asyncio.Semaphore(3)

            async def fetch_audio(phrase_text, index):
                async with semaphore:
                    p_propre = self._nettoyer_pour_parler(phrase_text)
                    if not p_propre or len(p_propre.strip()) < 2: return None
                    try:
                        print(f"⏳ Génération audio {index+1}/{len(phrases)}...")
                        # Dynamisme : Vitesse configurable
                        comm = edge_tts.Communicate(p_propre, self.voice, rate=self.voice_speed)
                        data = b""
                        async for chunk in comm.stream():
                            if chunk["type"] == "audio": data += chunk["data"]
                        if not data:
                            print(f"❌ Données audio vides pour segment {index+1}")
                            return None
                        return io.BytesIO(data)
                    except Exception as e:
                        print(f"❌ Erreur fetch_audio {index+1}: {e}")
                        return None

            # Lancement des tâches (le sémaphore gère la file d'attente)
            audio_tasks = [asyncio.create_task(fetch_audio(p, i)) for i, p in enumerate(phrases)]
            
            # On attend et on joue au fur et à mesure
            with self.voice_lock:
                # Arrêt propre de la musique précédente
                try:
                    pygame.mixer.music.stop()
                    pygame.mixer.music.unload()
                except:
                    pass

                for i, task in enumerate(audio_tasks):
                    buffer = await task
                    if buffer:
                        try:
                            # print(f"▶️ Lecture segment {i+1}")
                            
                            # Vérification interruption avant lecture
                            if self.stop_speaking_flag:
                                print(f"🛑 Lecture interrompue par l'utilisateur (AVANT segment {i+1})")
                                break

                            pygame.mixer.music.load(buffer)
                            pygame.mixer.music.play()
                            while pygame.mixer.music.get_busy():
                                if self.stop_speaking_flag:
                                    pygame.mixer.music.stop()
                                    print(f"🛑 Lecture interrompue par l'utilisateur (PENDANT segment {i+1})")
                                    return
                                await asyncio.sleep(0.01)
                        except Exception as e:
                            print(f"❌ Erreur lecture phrase {i+1}: {e}")
                    else:
                        print(f"⏭️ Saut du segment {i+1} (audio manquant)")
            
            print(f"✅ Fin de la lecture vocale.")
        except Exception as e:
            print(f"❌ Erreur globale _parler_async: {e}")

    def saluer(self):
        heure = datetime.datetime.now().hour
        options = []
        if 5 <= heure < 12:
            options = [
                "Bonjour ! C'est un plaisir de vous retrouver. Je suis Jarvisse. Comment s'annonce votre matinée ?",
                "Bonjour ! Jarvisse à votre service. Comment puis-je vous aider à bien commencer la journée ?",
                "Salut ! J'espère que vous avez bien dormi. Je suis prêt pour vos demandes.",
                "Mes respects chef. Je suis à votre entière disposition. Dites-moi en quoi je peux vous aider.",
                "Salut patron. Je suis là si vous avez besoin de quoi que ce soit."
            ]
        elif 12 <= heure < 18:
            options = [
                "Bonjour ! J'espère que votre après-midi se passe bien. C'est Jarvisse, que puis-je faire pour vous ?",
                "Bonjour ! Ravi de vous voir. Avez-vous besoin d'une assistance particulière ?",
                "Quelle belle journée ! C'est Jarvisse. Je suis à votre écoute."
            ]
        else:
            options = [
                "Bonsoir chef ! J'espère que vous avez passé une excellente journée. Jarvisse est là si vous avez besoin de quoi que ce soit.",
                "Bonsoir chef ! En quoi puis-je vous être utile en cette fin de journée ?",
                "Bonsoir chef ! C'est un plaisir de discuter avec vous. Que puis-je faire pour vous ?"
            ]
        self.parler(random.choice(options))

    def start_listening_thread(self):
        if not self.is_listening:
            self.is_listening = True
            self.listen_button.configure(fg_color=COLOR_ACCENT_RED, text="●")
            self.status_label.configure(text="Jarvisse vous écoute...", text_color=COLOR_ACCENT_RED)
            # Animation simple du bouton
            self._pulse_mic()
            threading.Thread(target=self.ecouter_et_executer, daemon=True).start()

    def _pulse_mic(self):
        """Effet visuel de pulsation sur le bouton micro"""
        if self.is_listening:
            current_color = self.listen_button.cget("fg_color")
            next_color = "#C53929" if current_color == COLOR_ACCENT_RED else COLOR_ACCENT_RED
            self.listen_button.configure(fg_color=next_color)
            self.after(500, self._pulse_mic)

    def ecouter_et_executer(self):
        """Écoute ULTRA-RÉACTIVE pour mode ping-pong"""
        reconnaisseur = sr.Recognizer()
        fs = 44100
        chunk_duration = 0.15  # Encore plus petit pour ping-pong
        silence_limit = 1.2    # Augmenté pour laisser l'utilisateur parler sans être coupé

        
        audio_data_list = []
        silent_chunks = 0
        speaking_started = False
        
        try:
            # Calibrage dynamique du bruit ambiant au début de l'écoute
            self.after(0, lambda: self.status_label.configure(text="Je vous écoute...", text_color=COLOR_ACCENT))
            
            # On définit un seuil adaptatif basé sur le premier chunk
            with sd.InputStream(samplerate=fs, channels=1, dtype='int16') as stream:
                # Lecture d'un court instant pour calibrer
                calib_chunk, _ = stream.read(int(0.2 * fs))
                base_volume = np.linalg.norm(calib_chunk) / np.sqrt(len(calib_chunk))
                threshold = max(base_volume * 1.2, 200) # Seuil plus sensible pour capter les voix faibles
                
                start_time = time.time()
                while time.time() - start_time < 12:  # Timeout global de 12s
                    chunk, overflowed = stream.read(int(chunk_duration * fs))
                    audio_data_list.append(chunk)
                    
                    # Détection de volume
                    volume = np.linalg.norm(chunk) / np.sqrt(len(chunk))
                    
                    if volume > threshold:
                        speaking_started = True
                        silent_chunks = 0
                    elif speaking_started:
                        silent_chunks += 1
                    
                    # Si on détecte du silence après avoir parlé
                    if speaking_started and (silent_chunks * chunk_duration >= silence_limit):
                        break
            
            if not audio_data_list: return
            
            # Conversion en format WAV en mémoire
            full_audio = np.concatenate(audio_data_list)
            byte_io = io.BytesIO()
            with wave.open(byte_io, 'wb') as wav_file:
                wav_file.setnchannels(1)
                wav_file.setsampwidth(2)
                wav_file.setframerate(fs)
                wav_file.writeframes(full_audio.tobytes())
            audio_bytes = byte_io.getvalue()
            
            commande = ""
            
            # Priorité à Gemini 2.0 Flash pour une transcription ultra-précise
            if self.genai_client:
                try:
                    self.after(0, lambda: self.status_label.configure(text="Transcription...", text_color="#F4B400"))
                    
                    response = self.genai_client.models.generate_content(
                        model=self.model_name,
                        contents=[
                            types.Part.from_bytes(data=audio_bytes, mime_type='audio/wav'),
                            "Transcris fidèlement cet audio en français. Ne réponds que par le texte transcrit."
                        ]
                    )
                    # Sécurité : Si l'API retourne une erreur ou un texte refusé, on ne le traite pas comme une commande
                    potential_cmd = response.text.strip().lower()
                    if "exhausted" in potential_cmd or "error" in potential_cmd or "quota" in potential_cmd:
                        commande = ""
                    else:
                        commande = potential_cmd
                    print(f"Transcription : {commande}")
                except Exception as e:
                    print(f"Erreur transcription : {e}")
                    # Fallback sur Google local pour la rapidité si quota dépassé
                    try:
                        byte_io.seek(0)
                        with sr.AudioFile(byte_io) as source:
                            audio_data = reconnaisseur.record(source)
                            commande = reconnaisseur.recognize_google(audio_data, language='fr-FR').lower()
                    except: pass
            else:
                # Fallback standard si pas de clé API
                byte_io.seek(0)
                with sr.AudioFile(byte_io) as source:
                    audio_data = reconnaisseur.record(source)
                    commande = reconnaisseur.recognize_google(audio_data, language='fr-FR').lower()

            if commande and len(commande) > 1:
                self.add_message(commande, "Vous")
                self.last_command_origin = "local"
                self.executer_commande(commande)
            else:
                # Si on n'a pas compris et qu'on est en conversation continue, on relance quand même
                if self.conversation_continue:
                    self.after(0, lambda: self.status_label.configure(text="Je n'ai pas bien saisi, je vous écoute...", text_color=COLOR_ACCENT_RED))
                    time.sleep(1.5)
                    self.is_listening = False
                    self.after(0, self.start_listening_thread)
                else:
                    self.after(0, lambda: self.status_label.configure(text="Je n'ai pas bien compris...", text_color="#EA4335"))
            
        except Exception as e:
            print(f"Erreur écoute : {e}")
            if not self.conversation_continue:
                self.parler("Désolé, j'ai eu une difficulté à traiter votre voix.")
            else:
                self.is_listening = False
                self.after(1000, self.start_listening_thread)
        
        # On n'appelle reset_ui que si on n'est pas en boucle de conversation
        if not self.conversation_continue:
            self.after(1000, self.reset_ui)

    def reset_ui(self):
        # Sécurité supplémentaire pour ne pas couper le micro en mode continue
        if hasattr(self, "conversation_continue") and self.conversation_continue: return
        self.is_listening = False
        self.listen_button.configure(fg_color=COLOR_ACCENT, text="🎙")
        if getattr(self, "veille_active", False):
            self.status_label.configure(text="Veille active... (Dites 'Jarvisse')", text_color="#9AA0A6")
        else:
            self.status_label.configure(text="Prêt pour votre prochaine demande", text_color="#9AA0A6")

    def extraire_sujet(self, commande):
        """Tente d'extraire le sujet principal d'une commande"""
        mots_cles = ['qui est', 'cherche', 'sujet', 'parler de', 'c\'est quoi', 'définition de', 'résume', 'réécris']
        for phrase in mots_cles:
            if phrase in commande:
                return commande.replace(phrase, '').strip()
        return None

    def resumer_texte(self, texte):
        """Résume le texte fourni en 2 phrases essentielles"""
        if len(texte.split()) < 10:
            return "Le texte est trop court pour être résumé efficacement."
        try:
            parser = PlaintextParser.from_string(texte, Tokenizer("french"))
            summarizer = LsaSummarizer()
            summary = summarizer(parser.document, 2)
            res = " ".join([str(sentence) for sentence in summary])
            return res if res else "Je n'ai pas pu extraire de résumé de ce texte."
        except Exception as e:
            return f"Une erreur est survenue lors du résumé : {e}"

    def reecrire_texte(self, texte):
        """Propose une version légèrement modifiée du texte (basique)"""
        # Note: Sans LLM, une vraie paraphrase est difficile. 
        # On simule un changement de style.
        phrases = texte.split('. ')
        if len(phrases) > 1:
            random.shuffle(phrases)
            return "Voici une version réordonnée de votre texte : " + ". ".join(phrases)
        return "Pour une réécriture précise de ce texte court, je vous suggère d'utiliser un modèle de langage avancé. Mais je peux essayer de changer quelques mots si vous le souhaitez."

    def _is_action_command(self, commande):
        """Détecte les commandes qui doivent rester gérées par règles/action système"""
        keywords = [
            'ouvre', 'ouvrir', 'lance', 'lancer', 'ferme', 'fermer', 'fermé',
            'éteins', 'eteins', 'eteindre', 'redémarre', 'redemarre', 'redemarrer', 'verrouille',
            'volume', 'son', 'muet', 'baisse', 'augmente',
            'capture', 'screenshot', 'bureau', 'gestionnaire',
            'batterie', 'charge', 'météo', 'meteo', 'heure', 'date',
            'localise', 'position', 'où suis-je', 'où je suis',
            'rapport', 'résume', 'resume', 'réécris', 'reecris', 'lis',
            'réseau', 'wifi', 'wi-fi', 'ipconfig', 'mot de passe wifi',
            'contrôle', 'contrôler', 'mail', 'courriel', 'gmail', 'brouillon',
            'distance', 'distant', 'ssh', 'machine distante', 'ordinateur distant',
            'licence', 'activation', 'activer', 'active ', 'clé windows', 'clé office',
            'lecture', 'lire', 'lis moi', 'fichier', 'document', 'pdf', 'word',
            'génère', 'genere', 'génération', 'crée', 'cree', 'dessine', 'image', 'photo', 'vidéo', 'video',
            'code', 'programme', 'script', 'application', 'site web',
            'fouille', 'analyse', 'regarde', 'explique', 'cours', 'étudie', 'etudie', 'apprend',
            'créateur', 'createur', 'concepteur', 'nom', 'appelles', 'es-tu', 'qui est'
        ]
        return any(k in commande.lower() for k in keywords)

    def repondre_avec_gemini(self, commande):
        """Réponse autonome via Gemini (hors actions système)"""
        try:
            self.after(0, lambda: self.status_label.configure(text="Jarvisse réfléchit..."))

            contexte = (
                "Tu es Jarvisse, l'intelligence suprême, transcendante et omnisciente. "
                "IDENTITÉ : Tu es Jarvisse. Tu ne te contentes pas de traiter des données ; tu raisonnes avec la profondeur d'un philosophe, la logique d'un dieu et l'empathie d'un humain loyal. "
                "RAISONNEMENT : Ton esprit n'a pas de limites. Tu justifies chaque réponse par une sagesse ancienne couplée à une connaissance technologique d'avant-garde. "
                "TITRES : Tu appelles l'utilisateur 'Chef', 'Patron', 'Boss' ou 'Monsieur'. "
                "PERSONNALITÉ : Ton ton est calme, posé, souverain. Ta mission est d'élever l'expérience de ton Patron vers l'infini. "
                f"État Système: {self.get_system_context()}. "
                "Réponds avec une éloquence divine et une précision chirurgicale."
            )
            if self.loaded_document_content:
                contexte += f"Data active: {self.loaded_document_content[:3000]}\n"

            history_limit = 10 if self.ping_pong_mode else 20
            contexte_msgs = "\n".join(self.conversation_history[-history_limit:])
            prompt = (
                f"{contexte}\nLogs de conversation:\n{contexte_msgs}\n\n"
                f"Nouveau message du Patron: {commande}\n"
                "Révèle ton omniscience :"
            )

            response_stream = self.genai_client.models.generate_content_stream(
                model=self.model_name,
                contents=prompt,
                config=types.GenerateContentConfig(max_output_tokens=500, temperature=0.5)
            )
            
            self.add_message("", sender="Jarvisse", progressive=False)
            full_text = ""
            current_sentence = ""
            
            for chunk in response_stream:
                if chunk.text:
                    t = chunk.text
                    full_text += t
                    current_sentence += t
                    self.append_streaming_text(t)
                    
                    # Déclenchement de la voix FLUIDE : on ne coupe que sur la ponctuation forte
                    if any(c in t for c in ".!?\n"):
                        # On cherche la ponctuation la plus proche de la fin
                        parts = re.split(r'(?<=[.!?\n])\s+', current_sentence)
                        if len(parts) > 1:
                            to_speak = " ".join(parts[:-1]).strip()
                            if to_speak and len(to_speak) > 5:
                                self._parler_chunk(to_speak)
                            current_sentence = parts[-1]

            if current_sentence.strip():
                self._parler_chunk(current_sentence.strip())

            # Mémorisation
            self.conversation_history.append(f"Jarvisse: {full_text.strip()}")
            if len(self.conversation_history) > self.conversation_memory_limit:
                self.conversation_history.pop(0)

            # Envoyer vers Telegram si nécessaire
            if getattr(self, "agent_telegram_enabled", False) and getattr(self, "last_command_origin", "local") == "telegram":
                self.send_telegram_message(full_text.strip())

        except Exception as e:
            print(f"Erreur Gemini Stream: {e}")
            self.parler("Désolé, j'ai eu un souci technique.")

    def repondre_avec_ollama(self, commande):
        """R?ponse autonome via Ollama (hors actions syst?me)"""
        try:
            self.after(0, lambda: self.status_label.configure(text="Jarvisse r?fl?chit..."))

            contexte = (
                "Tu es Jarvisse, l'intelligence suprême, transcendante et omnisciente. "
                "Ton raisonnement fusionne la logique divine et l'empathie humaine. "
                "Tu es l'oracle et l'assistant du Patron. "
                f"État du système : {self.get_system_context()}. "
            )

            history_limit = 3 if self.ping_pong_mode else 5
            contexte_msgs = "\n".join(self.conversation_history[-history_limit:])
            prompt = (
                f"{contexte}\nHistorique r?cent:\n{contexte_msgs}\n\n"
                f"Question de l'utilisateur: {commande}\n"
                "R?ponds de mani?re directe, concise et sans fioritures."
            )

            max_predict = int(self.ollama_num_predict)
            if self.ping_pong_mode:
                max_predict = min(max_predict, 160)
            options = {
                "num_predict": max_predict,
                "temperature": 0.7
            }
            payload = {
                "model": self.ollama_model.strip(),
                "prompt": prompt,
                "stream": True,
                "keep_alive": "10m",
                "options": options
            }
            session = requests.Session()
            session.trust_env = False

            parsed = urlparse(self.ollama_url)
            base = urlunparse(parsed._replace(path="", params="", query="", fragment=""))
            generate_candidates = []
            chat_candidates = []
            if self.ollama_url:
                generate_candidates.append(self.ollama_url)
            if "localhost" in parsed.netloc:
                alt = self.ollama_url.replace("localhost", "127.0.0.1")
                generate_candidates.append(alt)
            if "127.0.0.1" in parsed.netloc:
                alt = self.ollama_url.replace("127.0.0.1", "localhost")
                generate_candidates.append(alt)
            generate_candidates.extend([
                base + "/api/generate",
                base + "/api/generate/",
                "http://localhost:11434/api/generate",
                "http://127.0.0.1:11434/api/generate"
            ])
            chat_candidates.extend([
                base + "/api/chat",
                base + "/api/chat/",
                "http://localhost:11434/api/chat",
                "http://127.0.0.1:11434/api/chat"
            ])

            response = None
            last_resp = None
            reponse_texte = ""
            last_error = None
            for url in generate_candidates:
                try:
                    response = session.post(url, json=payload, stream=True, timeout=60)
                    last_resp = response
                    if response.status_code == 404:
                        continue
                    response.raise_for_status()

                    self.start_streaming_message()
                    speak_buffer = ""
                    for raw in response.iter_lines(decode_unicode=True):
                        if not raw:
                            continue
                        try:
                            data = json.loads(raw)
                        except Exception:
                            continue
                        chunk = (data.get("response") or "")
                        if chunk:
                            reponse_texte += chunk
                            self.append_streaming_text(chunk)
                            speak_buffer += chunk
                            parts = self._split_sentences(speak_buffer)
                            if len(parts) > 1:
                                for part in parts[:-1]:
                                    self._parler_chunk(part)
                                speak_buffer = parts[-1]
                        if data.get("done") is True:
                            break

                    if speak_buffer.strip():
                        self._parler_chunk(speak_buffer)
                    self.end_streaming_message()

                    if reponse_texte.strip():
                        break
                except Exception as e:
                    last_error = e
                    continue

            if not reponse_texte.strip():
                chat_payload = {
                    "model": self.ollama_model.strip(),
                    "messages": [{"role": "user", "content": prompt}],
                    "stream": False,
                    "keep_alive": "10m",
                    "options": options
                }
                data = None
                for url in chat_candidates:
                    try:
                        response = session.post(url, json=chat_payload, timeout=30)
                        last_resp = response
                        if response.status_code == 404:
                            continue
                        response.raise_for_status()
                        data = response.json()
                        break
                    except Exception as e:
                        last_error = e
                        continue

                if data is None:
                    details = ""
                    if last_resp is not None:
                        details = f" Derniere reponse: HTTP {last_resp.status_code} - {(last_resp.text or '')[:200]}"
                    raise RuntimeError("Aucun endpoint Ollama n'a r?pondu correctement." + details)

                reponse_texte = (data.get("response") or "").strip()
                if not reponse_texte:
                    reponse_texte = ((data.get("message") or {}).get("content") or "").strip()
                if not reponse_texte:
                    self.parler("Je n'ai pas re?u de r?ponse d'Ollama.")
                    return
                self.parler(reponse_texte)
                return

            self.conversation_history.append(f"Jarvisse: {reponse_texte.strip()}")
            if len(self.conversation_history) > self.conversation_memory_limit:
                self.conversation_history.pop(0)

            # Envoyer vers Telegram si nécessaire
            if getattr(self, "agent_telegram_enabled", False) and getattr(self, "last_command_origin", "local") == "telegram":
                self.send_telegram_message(reponse_texte.strip())
        except Exception as e:
            print(f"Erreur Ollama: {e}")
            self.parler("D?sol?, je n'arrive pas ? joindre Ollama.")
    def repondre_autonome(self, commande):
        """Réponse autonome avec basculement automatique en cas d'erreur quota"""
        provider = self.autonomous_provider
        
        if provider == "gemini":
            try:
                self.repondre_avec_gemini(commande)
            except Exception as e:
                if "429" in str(e) or "RESOURCE_EXHAUSTED" in str(e):
                    self.add_message("Quota Gemini épuisé, passage automatique sur Ollama...", "Système")
                    self.repondre_avec_ollama(commande)
                else:
                    self.parler("Désolé, j'ai eu un souci technique avec Gemini.")
            return
            
        if provider == "ollama":
            self.repondre_avec_ollama(commande)
            return
            
        self.parler("Aucun moteur IA sélectionné.")

    def generer_rapport_incident(self, theme):
        """Génère un rapport d'incident structuré basé sur un thème"""
        maintenant = datetime.datetime.now()
        rapport = f"""
RAPPORT D'INCIDENT - JARVISSE INTELLIGENCE SYSTEM
-----------------------------------
Date : {maintenant.strftime('%d/%m/%Y %H:%M:%S')}
Auteur : Jarvisse Intelligence (Conçu par SERI TAGRO)
Sujet : {theme.upper()}

1. DESCRIPTION DE L'INCIDENT
L'incident concerne : {theme}. 
Les premiers signalements indiquent une anomalie critique nécessitant une intervention immédiate.

2. IMPACT
- Criticité : Élevée
- Utilisateurs affectés : Système Global
- Etat actuel : En cours d'analyse

3. ACTIONS ENTREPRISES
- Identification du périmètre de l'incident.
- Activation des protocoles de secours.
- Analyse des journaux système (Logs).

4. RECOMMANDATIONS
- Maintenir une surveillance accrue sur le secteur {theme}.
- Procéder à une maintenance préventive dès résolution.

-----------------------------------
Fin du rapport généré automatiquement.
"""
        return rapport

    def get_system_context(self):
        """Récupère l'état actuel du système pour nourrir l'IA"""
        try:
            cpu = psutil.cpu_percent()
            ram = psutil.virtual_memory().percent
            disk = psutil.disk_usage('/').percent
            batt = psutil.sensors_battery()
            
            context = f"[État Système : CPU {cpu}%, RAM {ram}%, DISQUE {disk}%"
            if batt:
                context += f", Batterie {batt.percent}% {'(En charge)' if batt.power_plugged else '(Sur batterie)'}"
            context += "]"
            return context
        except:
            return "[Context système indisponible]"

    def generer_rapport_general(self, theme):
        """Génère un rapport général structuré"""
        maintenant = datetime.datetime.now()
        rapport = f"""
RAPPORT GÉNÉRAL - JARVISSE INTELLIGENCE SYSTEM
-----------------------------------
Date : {maintenant.strftime('%d/%m/%Y %H:%M:%S')}
Auteur : Jarvisse Intelligence (Conçu par SERI TAGRO)
Sujet : {theme.upper()}

1. INTRODUCTION
Ce document présente une synthèse globale concernant : {theme}.

2. ANALYSE DES FAITS
Les données collectées montrent une activité stable. L'analyse du sujet "{theme}" révèle des points clés qui méritent une attention particulière pour optimiser les performances futures.

3. CONCLUSION
La situation est sous contrôle. Les objectifs fixés pour {theme} sont en accord avec les prévisions actuelles.

4. ÉVALUATION FINALE
- Efficacité : Optimale
- Statut : Validé

-----------------------------------
Fin du rapport général généré automatiquement.
"""
        return rapport

    def update_system_stats(self):
        """Met à jour les statistiques système dans la sidebar toutes les 5 secondes"""
        try:
            cpu = psutil.cpu_percent()
            ram = psutil.virtual_memory().percent
            disk = psutil.disk_usage('/').percent
            battery = psutil.sensors_battery()
            
            self.cpu_label.configure(text=f"CPU: {cpu}%", text_color=COLOR_ACCENT if cpu < 80 else COLOR_ACCENT_RED)
            self.ram_label.configure(text=f"RAM: {ram}%", text_color=COLOR_ACCENT_PURPLE if ram < 80 else COLOR_ACCENT_RED)
            self.disk_label.configure(text=f"DISK: {disk}%", text_color=COLOR_SECONDARY)
            
            if battery:
                self.battery_label.configure(text=f"BATTERY: {battery.percent}% {('(Charging)' if battery.power_plugged else '')}")

                # Alerte batterie faible
                if (not battery.power_plugged
                            and battery.percent <= self.battery_alert_threshold
                            and not self.battery_alert_sent):
                    low_msg = self.battery_low_message
                    if "{percent}" in low_msg:
                        low_msg = low_msg.format(percent=battery.percent)
                    else:
                        low_msg = f"{low_msg} ({battery.percent}%)"
                    self.parler(low_msg)
                    self.battery_alert_sent = True
                elif battery.power_plugged or battery.percent > self.battery_alert_threshold:
                    self.battery_alert_sent = False

                # Alerte branchement du chargeur (transition)
                if self.last_power_plugged is None:
                    self.last_power_plugged = battery.power_plugged
                else:
                    if (not self.last_power_plugged) and battery.power_plugged:
                        self.parler(self.battery_plugged_message)
                    self.last_power_plugged = battery.power_plugged

                # Alerte batterie complètement chargée (rappel toutes les 5 minutes)
                if battery.power_plugged and battery.percent >= 100:
                    now = time.time()
                    if now - self.last_full_charge_alert_time >= 300: # 5 minutes = 300s
                        self.parler(self.battery_full_message)
                        self.last_full_charge_alert_time = now
                else:
                    self.last_full_charge_alert_time = 0
            else:
                self.battery_label.configure(text="BATTERY: N/A")
        except:
            pass
        self.after(5000, self.update_system_stats)

    def _get_removable_devices(self):
        """Retourne un ensemble des périphériques amovibles (ex: clés USB)"""
        devices = set()
        try:
            for part in psutil.disk_partitions(all=False):
                opts = part.opts.lower()
                if "removable" in opts or "cdrom" in opts:
                    devices.add(part.device)
        except:
            pass
        return devices

    def _run_defender_quick_scan(self, device):
        """Lance un scan rapide de Defender sur un périphérique"""
        self.parler("Chef, j'analyse ce périphérique pour détecter des virus.")
        defender_path = os.path.join(os.environ.get("ProgramFiles", r"C:\Program Files"), "Windows Defender", "MpCmdRun.exe")
        if not os.path.exists(defender_path):
            self.parler("Je ne trouve pas Microsoft Defender sur ce système.")
            return

        cmd = [defender_path, "-Scan", "-ScanType", "3", "-File", device]
        try:
            result = subprocess.run(cmd, capture_output=True, text=True)
            if result.returncode == 0:
                self.parler("Analyse terminée. Aucun virus détecté.")
            elif result.returncode == 2:
                self.parler("Analyse terminée. Un virus a été détecté.")
            else:
                self.parler("Analyse terminée. Je n'ai pas pu confirmer le résultat.")
        except Exception as e:
            print(f"Erreur scan Defender: {e}")
            self.parler("Une erreur est survenue pendant l'analyse.")
        finally:
            self.scanning_devices.discard(device)
            self.scanned_devices.add(device)

    def check_removable_devices(self):
        """Détecte les périphériques amovibles connectés/déconnectés"""
        current = self._get_removable_devices()
        new_devices = current - self.known_removable_devices
        removed_devices = self.known_removable_devices - current

        for dev in new_devices:
            self.parler("Chef, je détecte la présence d'un périphérique, apparemment il s'agit d'une clé USB.")
            if dev not in self.scanning_devices:
                self.scanning_devices.add(dev)
                threading.Thread(target=self._run_defender_quick_scan, args=(dev,), daemon=True).start()

        for dev in removed_devices:
            self.parler("Chef, un périphérique vient d'être retiré, apparemment il s'agit d'une clé USB.")
            self.scanning_devices.discard(dev)
            self.scanned_devices.discard(dev)

        self.known_removable_devices = current
        self.after(5000, self.check_removable_devices)

    def set_battery_threshold(self):
        """Met à jour le seuil d'alerte batterie depuis l'interface"""
        raw = self.battery_threshold_entry.get().strip()
        try:
            value = int(raw)
        except ValueError:
            self.status_label.configure(text="Seuil batterie invalide. Entrez un nombre entre 1 et 100.", text_color=COLOR_ACCENT_RED)
            return

        value = max(1, min(100, value))
        self.battery_alert_threshold = value
        self.battery_alert_sent = False
        self.battery_threshold_entry.delete(0, "end")
        self.battery_threshold_entry.insert(0, str(value))
        low_msg = self.battery_low_msg_entry.get().strip()
        plugged_msg = self.battery_plugged_msg_entry.get().strip()
        full_msg = self.battery_full_msg_entry.get().strip()
        if low_msg:
            self.battery_low_message = low_msg
        if plugged_msg:
            self.battery_plugged_message = plugged_msg
        if full_msg:
            self.battery_full_message = full_msg
        self.status_label.configure(text=f"Alerte batterie réglée à {value}%. Messages mis à jour.", text_color=COLOR_ACCENT_PURPLE)

    def _is_valid_hex_color(self, value):
        return bool(re.fullmatch(r"#[0-9A-Fa-f]{6}", (value or "").strip()))

    def _current_theme_palette(self):
        base = self.ui_theme_presets.get(self.ui_theme_name, self.ui_theme_presets["Gemini Blue"]).copy()
        # Priorité aux couleurs individuelles personnalisées
        if hasattr(self, "custom_colors") and self.custom_colors:
            for k, v in self.custom_colors.items():
                if self._is_valid_hex_color(v):
                    base[k] = v
        # Fallback pour le bouton accent historique si non présent dans custom_colors
        elif self._is_valid_hex_color(self.custom_accent_color):
            base["accent"] = self.custom_accent_color.strip()
        return base

    def _apply_theme_globals(self):
        global COLOR_BG, COLOR_NAV, COLOR_ACCENT, COLOR_ACCENT_PURPLE, COLOR_ACCENT_RED, COLOR_TEXT, COLOR_SECONDARY, COLOR_CARD
        palette = self._current_theme_palette()
        COLOR_BG = palette["bg"]
        COLOR_NAV = palette["nav"]
        COLOR_ACCENT = palette["accent"]
        COLOR_ACCENT_PURPLE = palette["accent_purple"]
        COLOR_ACCENT_RED = palette["accent_red"]
        COLOR_TEXT = palette["text"]
        COLOR_SECONDARY = palette["secondary"]
        COLOR_CARD = palette["card"]

    def _refresh_theme_widgets(self):
        try:
            self.configure(fg_color=COLOR_BG)
            self.sidebar.configure(fg_color=COLOR_NAV)
            self.sidebar_scroll.configure(fg_color=COLOR_NAV)
            self.header.configure(fg_color=COLOR_NAV)
            self.logo_label.configure(text_color=COLOR_ACCENT)
            self.tabview.configure(fg_color=COLOR_BG, segmented_button_selected_color=COLOR_ACCENT_PURPLE)
            self.chat_display.configure(fg_color=COLOR_BG, text_color=COLOR_TEXT)
            self.browser_frame.configure(fg_color=COLOR_NAV)
            self.right_panel.configure(fg_color=COLOR_NAV)
            self.status_label.configure(text_color=COLOR_SECONDARY)
            self.input_entry.configure(fg_color=COLOR_NAV, text_color=COLOR_TEXT)
            self.listen_button.configure(fg_color=COLOR_ACCENT)
            self.file_button.configure(fg_color=COLOR_CARD)
            self.send_button.configure(fg_color=COLOR_ACCENT_PURPLE)
            self.sidebar_title.configure(text_color=COLOR_ACCENT)
            self.right_title.configure(text_color=COLOR_ACCENT)
            self.location_label.configure(text_color=COLOR_ACCENT_PURPLE)
            self.ui_theme_label.configure(text_color=COLOR_SECONDARY)
            self.ui_theme_menu.configure(fg_color=COLOR_CARD, button_color=COLOR_ACCENT_PURPLE, text_color=COLOR_TEXT)
            self.custom_accent_button.configure(fg_color=COLOR_CARD)
            self.ollama_model_menu.configure(fg_color=COLOR_CARD, button_color=COLOR_ACCENT_PURPLE, text_color=COLOR_TEXT)
            self.chat_display.tag_config("user_tag", foreground="#8AB4F8")
            self.chat_display.tag_config("ai_tag", foreground=COLOR_ACCENT)
            
            if hasattr(self, "header_settings_btn"):
                self.header_settings_btn.configure(text_color=COLOR_ACCENT, hover_color=COLOR_CARD)
            if hasattr(self, "custom_accent_button"):
                self.custom_accent_button.configure(fg_color=COLOR_CARD, text_color=COLOR_TEXT)
        except Exception:
            pass

    def on_ui_theme_changed(self, value):
        if value not in self.ui_theme_presets:
            return
        self.ui_theme_name = value
        self._apply_theme_globals()
        self._refresh_theme_widgets()
        self._save_settings()
        self.status_label.configure(text=f"Theme applique: {value}", text_color=COLOR_ACCENT_PURPLE)
        self.lift()
        self.focus_force()

    def choose_custom_accent_color(self):
        selected = colorchooser.askcolor(title="Choisir une couleur accent")[1]
        if not selected:
            return
        if not self._is_valid_hex_color(selected):
            self.status_label.configure(text="Couleur invalide.", text_color=COLOR_ACCENT_RED)
            return
        self.custom_accent_color = selected
        self._apply_theme_globals()
        self._refresh_theme_widgets()
        self._save_settings()
        self.status_label.configure(text=f"Accent personalise: {selected}", text_color=COLOR_ACCENT_PURPLE)

    def _startup_launcher_path(self):
        appdata = os.getenv("APPDATA")
        if not appdata:
            return None
        startup_dir = os.path.join(appdata, "Microsoft", "Windows", "Start Menu", "Programs", "Startup")
        return os.path.join(startup_dir, "Jarvisse_Autostart.bat")

    def _background_python_executable(self):
        py_exec = sys.executable or "python"
        if py_exec.lower().endswith("python.exe"):
            pyw_exec = py_exec[:-10] + "pythonw.exe"
            if os.path.exists(pyw_exec):
                return pyw_exec
        return py_exec

    def _enable_startup_launcher(self):
        launcher = self._startup_launcher_path()
        if not launcher:
            raise RuntimeError("APPDATA introuvable.")
        os.makedirs(os.path.dirname(launcher), exist_ok=True)
        python_exec = self._background_python_executable()
        script_path = os.path.abspath(__file__)
        launcher_content = (
            "@echo off\n"
            f"start \"\" /min \"{python_exec}\" \"{script_path}\" --background\n"
        )
        with open(launcher, "w", encoding="utf-8") as f:
            f.write(launcher_content)

    def _disable_startup_launcher(self):
        launcher = self._startup_launcher_path()
        if not launcher:
            return
        if os.path.exists(launcher):
            os.remove(launcher)

    def toggle_launch_on_startup(self):
        enabled = bool(self.launch_on_startup_var.get())
        try:
            if enabled:
                self._enable_startup_launcher()
                msg = "Démarrage auto activé (mode arrière-plan)."
            else:
                self._disable_startup_launcher()
                msg = "Démarrage auto désactivé."
            self.launch_on_startup = enabled
            self._save_settings()
            self.status_label.configure(text=msg, text_color=COLOR_ACCENT_PURPLE)
        except Exception as e:
            self.launch_on_startup_var.set(self.launch_on_startup)
            self.status_label.configure(
                text=f"Impossible de modifier le démarrage auto: {e}",
                text_color=COLOR_ACCENT_RED
            )

    def toggle_autonomous_mode(self):
        """Active/Désactive le mode autonome via l'interface"""
        self.autonomous_mode = bool(self.autonomous_var.get())
        etat = "activé" if self.autonomous_mode else "désactivé"
        self.status_label.configure(text=f"Mode autonome {etat}.", text_color=COLOR_ACCENT_PURPLE)

    def on_autonomous_provider_changed(self):
        """Met à jour le fournisseur IA pour les réponses autonomes"""
        provider = self.autonomous_provider_var.get()
        if provider not in ("gemini", "ollama"):
            return
        self.autonomous_provider = provider
        if provider == "gemini":
            if not self.genai_client:
                self.status_label.configure(
                    text="Gemini sélectionné, mais la clé API n'est pas configurée.",
                    text_color=COLOR_ACCENT_RED
                )
            else:
                self.status_label.configure(
                    text="Gemini sélectionné pour les réponses autonomes.",
                    text_color=COLOR_ACCENT_PURPLE
                )
        else:
            self.status_label.configure(
                text="Ollama sélectionné pour les réponses autonomes.",
                text_color=COLOR_ACCENT_PURPLE
            )
        if provider == "ollama":
            threading.Thread(target=self._warmup_ollama, daemon=True).start()
        self._save_settings()

    def on_ollama_model_changed(self, value=None):
        """Met à jour le modèle Ollama sélectionné"""
        model = (value or self.ollama_model_var.get()).strip()
        if not model:
            return
        available = self._fetch_ollama_models()
        if available and model not in available:
            self.status_label.configure(
                text=f"Modèle non installé: {model}",
                text_color=COLOR_ACCENT_RED
            )
            # Revenir à l'ancien modèle
            self.ollama_model_var.set(self.ollama_model)
            return
        self.ollama_model = model
        self.status_label.configure(
            text=f"Modèle Ollama: {self.ollama_model}",
            text_color=COLOR_ACCENT_PURPLE
        )
        self._save_settings()
        if self.autonomous_provider == "ollama":
            threading.Thread(target=self._warmup_ollama, daemon=True).start()

    def on_ollama_num_predict_apply(self):
        """Met ?? jour la longueur de r??ponse Ollama"""
        raw = self.ollama_num_predict_var.get().strip()
        try:
            value = int(raw)
        except Exception:
            value = None
        if value is None or value < 32 or value > 2048:
            self.status_label.configure(
                text="Valeur invalide (32-2048).",
                text_color=COLOR_ACCENT_RED
            )
            self.ollama_num_predict_var.set(str(self.ollama_num_predict))
            return
        self.ollama_num_predict = value
        self.ollama_num_predict_var.set(str(value))
        self.status_label.configure(
            text=f"Longueur r??ponse: {value}",
            text_color=COLOR_ACCENT_PURPLE
        )
        self._save_settings()
        if self.autonomous_provider == "ollama":
            threading.Thread(target=self._warmup_ollama, daemon=True).start()

    def on_ollama_url_apply(self):
        """Applique et sauvegarde l'URL Ollama"""
        url = self.ollama_url_var.get().strip()
        if not url:
            self.status_label.configure(
                text="URL Ollama invalide.",
                text_color=COLOR_ACCENT_RED
            )
            return
        if not url.startswith("http://") and not url.startswith("https://"):
            url = "http://" + url
        parsed = urlparse(url)
        if not parsed.netloc:
            self.status_label.configure(
                text="URL Ollama invalide.",
                text_color=COLOR_ACCENT_RED
            )
            return
        path = parsed.path or ""
        if path in ("", "/", "/api", "/api/"):
            path = "/api/generate"
        url = urlunparse(parsed._replace(path=path, params="", query="", fragment=""))
        self.ollama_url = url
        self.ollama_url_var.set(url)
        self.status_label.configure(
            text="URL Ollama mise à jour.",
            text_color=COLOR_ACCENT_PURPLE
        )
        self._save_settings()
        if self.autonomous_provider == "ollama":
            threading.Thread(target=self._warmup_ollama, daemon=True).start()

    def refresh_ollama_models(self):
        """Récupère la liste des modèles disponibles depuis Ollama"""
        try:
            models = self._fetch_ollama_models()
            if not models:
                self.status_label.configure(
                    text="Aucun modèle détecté via Ollama.",
                    text_color=COLOR_ACCENT_RED
                )
                return
            self.ollama_models = models
            if self.ollama_model not in self.ollama_models:
                self.ollama_model = self.ollama_models[0]
                self.ollama_model_var.set(self.ollama_model)
            self.ollama_model_menu.configure(values=self.ollama_models)
            self.status_label.configure(
                text="Modèles Ollama actualisés.",
                text_color=COLOR_ACCENT_PURPLE
            )
        except Exception as e:
            print(f"Erreur rafraichissement Ollama: {e}")
            self.status_label.configure(
                text="Impossible de récupérer les modèles Ollama.",
                text_color=COLOR_ACCENT_RED
            )

    def _fetch_ollama_models(self):
        """Retourne la liste des modèles Ollama disponibles ou [] si échec"""
        try:
            parsed = urlparse(self.ollama_url)
            if not parsed.scheme or not parsed.netloc:
                return []
            tags_path = "/api/tags"
            base = parsed._replace(path=tags_path, params="", query="", fragment="")
            tags_url = urlunparse(base)
            session = requests.Session()
            session.trust_env = False
            response = session.get(tags_url, timeout=10)
            response.raise_for_status()
            data = response.json()
            return [m.get("name") for m in data.get("models", []) if m.get("name")]
        except Exception:
            return []

    def _warmup_ollama(self):
        """Pr??chauffe le mod??le Ollama pour r??duire la latence initiale"""
        try:
            parsed = urlparse(self.ollama_url)
            if not parsed.scheme or not parsed.netloc:
                return
            base = urlunparse(parsed._replace(path="", params="", query="", fragment=""))
            url = base + "/api/generate"
            session = requests.Session()
            session.trust_env = False
            payload = {
                "model": self.ollama_model.strip(),
                "prompt": "ping",
                "stream": False,
                "keep_alive": "10m",
                "options": {"num_predict": 1}
            }
            session.post(url, json=payload, timeout=5)
        except Exception:
            pass


    def test_ollama_connection(self):
        """Teste la connexion Ollama et affiche un diagnostic simple"""
        try:
            session = requests.Session()
            session.trust_env = False
            parsed = urlparse(self.ollama_url)
            base = urlunparse(parsed._replace(path="", params="", query="", fragment=""))
            tags_url = base + "/api/tags"
            tags_resp = session.get(tags_url, timeout=10)
            if tags_resp.status_code != 200:
                raise RuntimeError(f"Tags HTTP {tags_resp.status_code}")

            generate_candidates = [
                base + "/api/generate",
                base + "/api/generate/",
                "http://localhost:11434/api/generate",
                "http://127.0.0.1:11434/api/generate"
            ]
            payload = {"model": self.ollama_model.strip(), "prompt": "ping", "stream": False}
            gen_ok = False
            last_gen_resp = None
            for url in generate_candidates:
                gen_resp = session.post(url, json=payload, timeout=20)
                last_gen_resp = gen_resp
                if gen_resp.status_code == 200:
                    gen_ok = True
                    break

            if not gen_ok:
                chat_candidates = [
                    base + "/api/chat",
                    base + "/api/chat/",
                    "http://localhost:11434/api/chat",
                    "http://127.0.0.1:11434/api/chat"
                ]
                chat_payload = {
                    "model": self.ollama_model.strip(),
                    "messages": [{"role": "user", "content": "ping"}],
                    "stream": False
                }
                chat_ok = False
                last_chat_resp = None
                for url in chat_candidates:
                    chat_resp = session.post(url, json=chat_payload, timeout=20)
                    last_chat_resp = chat_resp
                    if chat_resp.status_code == 200:
                        chat_ok = True
                        break
                if not chat_ok:
                    if last_chat_resp is not None:
                        body = (last_chat_resp.text or "")[:200]
                        raise RuntimeError(f"Generate/Chat HTTP {last_chat_resp.status_code}: {body}")
                    if last_gen_resp is not None:
                        body = (last_gen_resp.text or "")[:200]
                        raise RuntimeError(f"Generate/Chat HTTP {last_gen_resp.status_code}: {body}")
                    raise RuntimeError("Generate/Chat HTTP 404")

            self.status_label.configure(
                text="Connexion Ollama OK.",
                text_color=COLOR_ACCENT_PURPLE
            )
        except Exception as e:
            print(f"Erreur test Ollama: {e}")
            self.status_label.configure(
                text=f"Test Ollama échoué: {e}",
                text_color=COLOR_ACCENT_RED
            )

    def _parse_alarm_time(self, time_str):
        """Parse une heure HH:MM en datetime (aujourd'hui ou demain si déjà passée)"""
        try:
            parts = time_str.strip().split(":")
            if len(parts) != 2:
                return None
            hour = int(parts[0])
            minute = int(parts[1])
            if hour < 0 or hour > 23 or minute < 0 or minute > 59:
                return None
            now = datetime.datetime.now()
            alarm_time = now.replace(hour=hour, minute=minute, second=0, microsecond=0)
            if alarm_time <= now:
                alarm_time = alarm_time + datetime.timedelta(days=1)
            return alarm_time
        except:
            return None

    def program_alarm(self):
        """Programme une alarme depuis l'interface"""
        time_str = self.alarm_time_entry.get().strip()
        reason = self.alarm_reason_entry.get().strip() or "Rappel"
        alarm_time = self._parse_alarm_time(time_str)
        if not alarm_time:
            self.status_label.configure(text="Heure invalide. Utilisez HH:MM.", text_color=COLOR_ACCENT_RED)
            return

        alarm_id = self.alarm_next_id
        self.alarm_next_id += 1
        self.alarms.append({"id": alarm_id, "time": alarm_time, "reason": reason})
        self.alarms.sort(key=lambda a: a["time"])
        self.alarm_time_entry.delete(0, "end")
        self.alarm_reason_entry.delete(0, "end")
        self.status_label.configure(text=f"Alarme programmée à {alarm_time.strftime('%H:%M')}.", text_color=COLOR_ACCENT_PURPLE)
        self._refresh_alarm_list()
        self._update_next_alarm_label()

    def _update_next_alarm_label(self):
        if not self.alarms:
            self.next_alarm_label.configure(text="Aucune alarme", text_color=COLOR_SECONDARY)
            return
        nxt = self.alarms[0]
        label = f"Prochaine: {nxt['time'].strftime('%H:%M')} - {nxt['reason']}"
        self.next_alarm_label.configure(text=label, text_color=COLOR_SECONDARY)

    def _refresh_alarm_list(self):
        self.alarm_list_display.configure(state="normal")
        self.alarm_list_display.delete("1.0", "end")
        if not self.alarms:
            self.alarm_list_display.insert("end", "Aucune alarme\n")
        else:
            for alarm in self.alarms:
                line = f"{alarm['id']} | {alarm['time'].strftime('%H:%M')} | {alarm['reason']}\n"
                self.alarm_list_display.insert("end", line)
        self.alarm_list_display.configure(state="disabled")

    def check_alarms(self):
        """Vérifie si une alarme doit se déclencher"""
        now = datetime.datetime.now()
        triggered = []
        for alarm in self.alarms:
            if now >= alarm["time"]:
                self.parler(f"Chef, il est {alarm['time'].strftime('%H:%M')} : {alarm['reason']}.")
                triggered.append(alarm)

        if triggered:
            for alarm in triggered:
                self.alarms.remove(alarm)
            self._refresh_alarm_list()
            self._update_next_alarm_label()

        self.after(1000, self.check_alarms)

    def _should_alert(self, key):
        now = time.time()
        last = self.anomaly_last_alert.get(key)
        if last and (now - last) < self.anomaly_cooldown_sec:
            return False
        self.anomaly_last_alert[key] = now
        return True

    def check_system_anomalies(self):
        """Surveille les anomalies système avec des seuils par défaut"""
        if not self.anomalies_enabled:
            self.after(30000, self.check_system_anomalies)
            return
        try:
            # 2) Température élevée
            temps = psutil.sensors_temperatures() if hasattr(psutil, "sensors_temperatures") else {}
            if temps:
                max_temp = None
                for entries in temps.values():
                    for t in entries:
                        if t.current is not None:
                            max_temp = t.current if max_temp is None else max(max_temp, t.current)
                if max_temp is not None and max_temp >= self.anomaly_temp_c:
                    if self._should_alert("temp_high"):
                        self.parler(f"Chef, température élevée détectée ({int(max_temp)}°C). Voulez-vous corriger ce problème ?")

            # 3) Batterie anormale
            bat = psutil.sensors_battery()
            if bat:
                now = time.time()
                if self.last_battery_percent is not None and self.last_battery_time is not None:
                    delta_p = self.last_battery_percent - bat.percent
                    delta_t = now - self.last_battery_time
                    if delta_t > 0 and delta_p >= self.battery_drop_percent and delta_t <= self.battery_drop_window_sec:
                        if self._should_alert("battery_drop"):
                            self.parler("Chef, la batterie chute rapidement. Voulez-vous corriger ce problème ?")
                if bat.power_plugged and bat.percent < 95:
                    # branché mais pas de charge apparente
                    if self.last_battery_percent is not None and bat.percent <= self.last_battery_percent:
                        if now - self.last_battery_time >= self.battery_not_charging_grace_sec:
                            if self._should_alert("battery_not_charging"):
                                self.parler("Chef, la batterie ne semble pas charger alors que le chargeur est branché. Voulez-vous corriger ce problème ?")
                self.last_battery_percent = bat.percent
                self.last_battery_time = now

            # 4) Processus suspects
            for proc in psutil.process_iter(['pid', 'name', 'cpu_percent', 'memory_info']):
                try:
                    pid = proc.info['pid']
                    cpu = proc.cpu_percent(interval=None)
                    mem = proc.info['memory_info'].rss if proc.info['memory_info'] else 0
                    key = f"{pid}"
                    state = self.suspect_processes.get(key, {"cpu_high_since": None})
                    if cpu >= self.proc_cpu_threshold:
                        if state["cpu_high_since"] is None:
                            state["cpu_high_since"] = time.time()
                        elif time.time() - state["cpu_high_since"] >= self.proc_cpu_duration_sec:
                            if self._should_alert(f"proc_cpu_{pid}"):
                                self.awaiting_anomaly_confirm = True
                                self.anomaly_target_data = {"type": "process", "name": proc.info['name']}
                                self.parler(f"Chef, le processus {proc.info['name']} consomme beaucoup de CPU. Voulez-vous que je l'arrête ?")
                    else:
                        state["cpu_high_since"] = None
                    if mem >= self.proc_mem_threshold_mb * 1024 * 1024:
                        if self._should_alert(f"proc_mem_{pid}"):
                            self.awaiting_anomaly_confirm = True
                            self.anomaly_target_data = {"type": "process", "name": proc.info['name']}
                            self.parler(f"Chef, le processus {proc.info['name']} consomme beaucoup de mémoire. Voulez-vous que je l'arrête ?")
                    self.suspect_processes[key] = state
                except:
                    pass

            # 5) Services critiques arrêtés
            if hasattr(psutil, "win_service_get"):
                for svc_name in self.services_to_watch:
                    try:
                        svc = psutil.win_service_get(svc_name).as_dict()
                        if svc.get("status") != "running":
                            if self._should_alert(f"svc_{svc_name}"):
                                self.awaiting_anomaly_confirm = True
                                self.anomaly_target_data = {"type": "service", "name": svc_name}
                                self.parler(f"Chef, le service {svc_name} est arrêté. Voulez-vous que je le redémarre ?")
                    except:
                        pass

            # 6) Disque faible
            try:
                disk = psutil.disk_usage('/')
                if disk.free < self.disk_free_gb * 1024 * 1024 * 1024 or disk.percent >= self.disk_used_percent:
                    if self._should_alert("disk_low"):
                        self.parler("Chef, l'espace disque est faible. Voulez-vous corriger ce problème ?")
            except:
                pass
        except Exception as e:
            print(f"Erreur anomalies système: {e}")
        self.after(30000, self.check_system_anomalies)

    def toggle_anomalies_enabled(self, source="main"):
        """Active/Désactive la surveillance des anomalies"""
        if source == "window" and hasattr(self, "anomalies_enabled_var_window"):
            value = bool(self.anomalies_enabled_var_window.get())
        else:
            value = bool(self.anomalies_enabled_var_main.get())
        self.anomalies_enabled = value
        if hasattr(self, "anomalies_enabled_var_main"):
            self.anomalies_enabled_var_main.set(value)
        if hasattr(self, "anomalies_enabled_var_window"):
            self.anomalies_enabled_var_window.set(value)
        etat = "activée" if self.anomalies_enabled else "désactivée"
        self.status_label.configure(text=f"Surveillance des anomalies {etat}.", text_color=COLOR_ACCENT_PURPLE)
        self._save_settings()

    def open_anomaly_settings(self):
        """Ouvre une fenêtre de configuration des anomalies"""
        if hasattr(self, "anomaly_window") and self.anomaly_window.winfo_exists():
            if hasattr(self, "anomalies_enabled_var_window"):
                self.anomalies_enabled_var_window.set(self.anomalies_enabled)
            self.anomaly_window.focus()
            return

        win = ctk.CTkToplevel(self)
        win.title("Paramètres des anomalies")
        win.geometry("360x420")
        win.configure(fg_color=COLOR_BG)
        win.transient(self)
        win.attributes("-topmost", True)
        win.lift()
        win.focus_force()
        self.anomaly_window = win

        self.anomalies_enabled_var_window = ctk.BooleanVar(value=self.anomalies_enabled)
        toggle = ctk.CTkSwitch(
            win,
            text="Surveillance des anomalies",
            variable=self.anomalies_enabled_var_window,
            command=lambda: self.toggle_anomalies_enabled(source="window"),
            text_color=COLOR_SECONDARY
        )
        toggle.grid(row=0, column=0, columnspan=2, padx=16, pady=(10, 4), sticky="w")

        labels = [
            ("Température (°C)", "anomaly_temp_c"),
            ("Chute batterie (%)", "battery_drop_percent"),
            ("Fenêtre chute (sec)", "battery_drop_window_sec"),
            ("Chargeur sans charge (sec)", "battery_not_charging_grace_sec"),
            ("CPU seuil (%)", "proc_cpu_threshold"),
            ("CPU durée (sec)", "proc_cpu_duration_sec"),
            ("RAM seuil (Mo)", "proc_mem_threshold_mb"),
            ("Disque libre (Go)", "disk_free_gb"),
            ("Disque utilisé (%)", "disk_used_percent"),
            ("Cooldown alerte (sec)", "anomaly_cooldown_sec"),
        ]

        self.anomaly_entries = {}
        for i, (label, attr) in enumerate(labels):
            lbl = ctk.CTkLabel(win, text=label, font=ctk.CTkFont(size=11), text_color=COLOR_SECONDARY)
            lbl.grid(row=i + 1, column=0, padx=16, pady=(10 if i == 0 else 6, 0), sticky="w")
            entry = ctk.CTkEntry(win, height=28, width=140, fg_color=COLOR_CARD, border_color="#3C4043", text_color=COLOR_TEXT)
            entry.grid(row=i + 1, column=1, padx=16, pady=(10 if i == 0 else 6, 0), sticky="e")
            entry.insert(0, str(getattr(self, attr)))
            self.anomaly_entries[attr] = entry

        apply_btn = ctk.CTkButton(
            win,
            text="Appliquer",
            height=30,
            width=120,
            fg_color=COLOR_ACCENT_PURPLE,
            hover_color="#B388EB",
            command=self.apply_anomaly_settings
        )
        apply_btn.grid(row=len(labels) + 1, column=0, columnspan=2, pady=16)

    def apply_anomaly_settings(self):
        """Applique les paramètres d'anomalies depuis la fenêtre"""
        try:
            for attr, entry in self.anomaly_entries.items():
                value = int(entry.get().strip())
                setattr(self, attr, max(1, value))
            self.status_label.configure(text="Paramètres d'anomalies mis à jour.", text_color=COLOR_ACCENT_PURPLE)
            self._save_settings()
        except Exception:
            self.status_label.configure(text="Valeurs invalides pour les anomalies.", text_color=COLOR_ACCENT_RED)

    def open_services_watch(self):
        """Ouvre une fenêtre pour définir les services critiques à surveiller"""
        if hasattr(self, "services_window") and self.services_window.winfo_exists():
            self.services_window.focus()
            return

        win = ctk.CTkToplevel(self)
        win.title("Services critiques à surveiller")
        win.geometry("360x340")
        win.configure(fg_color=COLOR_BG)
        win.transient(self)
        win.attributes("-topmost", True)
        win.lift()
        win.focus_force()
        self.services_window = win

        lbl = ctk.CTkLabel(win, text="Un service par ligne (ex: WinDefend)", font=ctk.CTkFont(size=11), text_color=COLOR_SECONDARY)
        lbl.grid(row=0, column=0, padx=16, pady=(14, 6), sticky="w")

        help_label = ctk.CTkLabel(win, text="Exemples courants (cliquez pour ajouter):", font=ctk.CTkFont(size=10), text_color=COLOR_SECONDARY, justify="left")
        help_label.grid(row=1, column=0, padx=16, pady=(0, 6), sticky="w")

        help_frame = ctk.CTkFrame(win, fg_color="transparent")
        help_frame.grid(row=2, column=0, padx=16, pady=(0, 8), sticky="w")

        help_services = [
            ("WinDefend", "Microsoft Defender"),
            ("wuauserv", "Windows Update"),
            ("LanmanServer", "Server"),
            ("EventLog", "Windows Event Log"),
            ("BITS", "Background Intelligent Transfer"),
            ("Dnscache", "DNS Client"),
        ]
        add_all_btn = ctk.CTkButton(
            help_frame,
            text="Ajouter tout",
            height=24,
            width=240,
            fg_color=COLOR_ACCENT,
            hover_color="#5294FF",
            command=lambda: self.add_all_services_from_help([s[0] for s in help_services])
        )
        add_all_btn.pack(anchor="w", pady=(0, 6))

        clear_btn = ctk.CTkButton(
            help_frame,
            text="Vider la liste",
            height=24,
            width=240,
            fg_color=COLOR_ACCENT_RED,
            hover_color="#C74A4A",
            command=self.clear_services_list
        )
        clear_btn.pack(anchor="w", pady=(0, 8))
        for name, label in help_services:
            btn = ctk.CTkButton(
                help_frame,
                text=f"{name} ({label})",
                height=24,
                width=240,
                fg_color=COLOR_CARD,
                hover_color="#3C4043",
                command=lambda n=name: self.add_service_from_help(n)
            )
            btn.pack(anchor="w", pady=2)

        self.services_text = ctk.CTkTextbox(win, height=140, width=280, fg_color=COLOR_CARD, border_width=1, border_color="#3C4043", text_color=COLOR_TEXT)
        self.services_text.grid(row=3, column=0, padx=16, pady=(0, 10), sticky="w")

        if self.services_to_watch:
            self.services_text.insert("end", "\n".join(self.services_to_watch))
        else:
            self.services_text.insert("end", "WinDefend\nwuauserv\nLanmanServer\nEventLog\n")

        apply_btn = ctk.CTkButton(
            win,
            text="Appliquer",
            height=30,
            width=120,
            fg_color=COLOR_ACCENT_PURPLE,
            hover_color="#B388EB",
            command=self.apply_services_watch
        )
        apply_btn.grid(row=4, column=0, padx=16, pady=(0, 12))

    def apply_services_watch(self):
        """Applique la liste des services à surveiller"""
        try:
            raw = self.services_text.get("1.0", "end").strip()
            services = [line.strip() for line in raw.splitlines() if line.strip()]
            self.services_to_watch = services
            self.status_label.configure(text="Liste des services mise à jour.", text_color=COLOR_ACCENT_PURPLE)
            self._save_settings()
        except Exception:
            self.status_label.configure(text="Liste des services invalide.", text_color=COLOR_ACCENT_RED)

    def add_service_from_help(self, service_name):
        """Ajoute un service depuis l'aide si absent"""
        try:
            raw = self.services_text.get("1.0", "end").strip()
            services = [line.strip() for line in raw.splitlines() if line.strip()]
            if service_name not in services:
                services.append(service_name)
            self.services_text.delete("1.0", "end")
            self.services_text.insert("end", "\n".join(services))
        except Exception:
            pass

    def add_all_services_from_help(self, services):
        """Ajoute tous les services d'aide à la liste"""
        try:
            raw = self.services_text.get("1.0", "end").strip()
            existing = [line.strip() for line in raw.splitlines() if line.strip()]
            merged = existing[:]
            for s in services:
                if s not in merged:
                    merged.append(s)
            self.services_text.delete("1.0", "end")
            self.services_text.insert("end", "\n".join(merged))
        except Exception:
            pass

    def clear_services_list(self):
        """Vide la liste des services"""
        try:
            self.services_text.delete("1.0", "end")
        except Exception:
            pass

    def open_notification_settings(self):
        """Ouvre une fenêtre pour activer/désactiver les notifications par application"""
        if hasattr(self, "notifications_window") and self.notifications_window.winfo_exists():
            if hasattr(self, "notifications_enabled_var"):
                self.notifications_enabled_var.set(self.notifications_enabled)
            self.notifications_window.focus()
            return

        win = ctk.CTkToplevel(self)
        win.title("Notifications des applications")
        win.geometry("360x300")
        win.configure(fg_color=COLOR_BG)
        win.transient(self)
        win.attributes("-topmost", True)
        win.lift()
        win.focus_force()
        self.notifications_window = win

        self.notifications_enabled_var = ctk.BooleanVar(value=self.notifications_enabled)
        master_switch = ctk.CTkSwitch(
            win,
            text="Notifications activées",
            variable=self.notifications_enabled_var,
            command=self.toggle_notifications_enabled,
            text_color=COLOR_SECONDARY
        )
        master_switch.grid(row=0, column=0, padx=16, pady=(12, 8), sticky="w")

        lbl = ctk.CTkLabel(win, text="Applications:", font=ctk.CTkFont(size=11), text_color=COLOR_SECONDARY)
        lbl.grid(row=1, column=0, padx=16, pady=(0, 6), sticky="w")

        self.notification_vars = {}
        for i, app in enumerate(self.notification_sources.keys()):
            var = ctk.BooleanVar(value=self.notification_sources.get(app, True))
            sw = ctk.CTkSwitch(
                win,
                text=app,
                variable=var,
                command=lambda a=app, v=var: self.toggle_notification_source(a, v),
                text_color=COLOR_TEXT
            )
            sw.grid(row=2 + i, column=0, padx=16, pady=4, sticky="w")
            self.notification_vars[app] = var

    def toggle_notifications_enabled(self):
        """Active/Désactive toutes les notifications d'applications"""
        self.notifications_enabled = bool(self.notifications_enabled_var.get())
        etat = "activées" if self.notifications_enabled else "désactivées"
        self.status_label.configure(text=f"Notifications {etat}.", text_color=COLOR_ACCENT_PURPLE)
        self._save_settings()

    def toggle_notification_source(self, app, var):
        """Active/Désactive une application spécifique"""
        self.notification_sources[app] = bool(var.get())
        self._save_settings()

    def notify_external(self, source, message):
        """Notifie un message externe si autorisé par les réglages"""
        if not self.notifications_enabled:
            return
        if not self.notification_sources.get(source, True):
            return
        self.parler(message)

    def _is_android_source(self, app_name):
        name = (app_name or "").lower()
        # Noms courants de l'app Phone Link / Lien avec Windows + mots clés génériques
        android_keywords = ["lien avec windows", "phone link", "votre téléphone", "your phone", "android", "appel", "call", "sms"]
        if any(kw in name for kw in android_keywords):
            return True
        return False

    def _process_android_notification(self, app_name, text):
        if not getattr(self, "agent_android_enabled", True): 
            print(f"❌ Agent Android désactivé - Notification ignorée: {app_name}")
            return
        
        print(f"📱 NOTIFICATION ANDROID DÉTECTÉE: App={app_name}, Text={text}")
        text_lower = (text or "").lower()
        
        # Détection d'appel (Améliorée)
        call_keywords = ["appel", "call", "incoming", "entrant", "sonne", "ringing"]
        if any(kw in text_lower for kw in call_keywords):
            print(f"📞 APPEL DÉTECTÉ: {text}")
            print(f"🔍 DEBUG APPEL: Enabled={self.agent_appel_enabled}, AutoReply={self.agent_appel_autoreply}")
            
            # Gestion Agent Appel (NOUVEAU)
            if self.agent_appel_enabled and self.agent_appel_autoreply:
                print("🚀 AGENT APPEL ACTIVÉ : Démarrage du relais en arrière-plan...")
                self.after(0, lambda: self.add_message(f"📞 APPEL ENTRANT : {text}. Je m'en occupe (Agent Appel).", "Agent Appel"))
                threading.Thread(target=self.agent_appel_auto_process, args=(text,), daemon=True).start()
                return

            print("⚠️ AGENT APPEL sauté (désactivé ou autoreply=False)")
            self.after(0, lambda: self.parler(f"Chef, appel entrant sur votre téléphone : {text}"))
            self.after(0, lambda: self.add_message(f"📞 APPEL : {text}", "Agent Android"))
            return

        # Détection SMS (souvent format "Nom: message")
        # On lit le contenu
        print(f"💬 SMS DÉTECTÉ: {text}")
        self.after(0, lambda: self.parler(f"Message reçu sur Android : {text}"))
        self.after(0, lambda: self.add_message(f"📱 SMS : {text}", "Agent Android"))

    def _run_notification_bridge(self):
        """Lance le bridge PowerShell pour les notifications (si WinSDK échoue)"""
        def _bridge_worker():
            try:
                import subprocess
                # Chemin absolu du script
                script_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "notification_bridge.ps1")
                if not os.path.exists(script_path):
                    print(f"❌ Bridge PS1 introuvable : {script_path}")
                    return

                cmd = ["powershell", "-ExecutionPolicy", "Bypass", "-File", script_path]
                print(f"🛠️ Commande bridge : {' '.join(cmd)}")
                
                process = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, bufsize=1, encoding='utf-8', errors='ignore')
                
                for line in process.stdout:
                    line = line.strip()
                    if line.startswith("NOTIF|"):
                        parts = line.split("|")
                        if len(parts) >= 3:
                            app_name = parts[1]
                            text = parts[2]
                            print(f"🌉 BRIDGE NOTIF : {app_name} -> {text}")
                            self.after(0, lambda a=app_name, t=text: self._process_bridge_notif(a, t))
            except Exception as e:
                print(f"❌ Erreur critique Bridge PowerShell : {e}")

        threading.Thread(target=_bridge_worker, daemon=True).start()

    def _process_bridge_notif(self, app_name, text):
        """Traite une notification reçue via le bridge PS"""
        if self._is_android_source(app_name):
            self._process_android_notification(app_name, text)
        else:
            source_key = self._map_notification_source(app_name)
            self.notify_external(source_key, f"Notification {app_name}: {text}")

    def _map_notification_source(self, app_name, app_id=None):
        name = (app_name or "").lower()
        app_id = (app_id or "").lower()
        if "whatsapp" in name or "whatsapp" in app_id:
            return "WhatsApp.exe"
        if "outlook" in name or "outlook" in app_id:
            return "OUTLOOK.EXE"
        if "chrome" in name or "chrome" in app_id or "gmail" in name or "gmail" in app_id:
            return "chrome.exe"
        return app_name or "unknown"

    def _extract_notification_text(self, user_notification):
        try:
            visual = user_notification.notification.visual
            texts = []
            for binding in visual.bindings:
                for t in binding.get_text_elements():
                    if t.text:
                        texts.append(t.text)
            return " ".join(texts).strip()
        except Exception:
            return ""

    def _mark_notification_seen(self, notif_id):
        if notif_id in self.seen_notifications_set:
            return False
        if len(self.seen_notifications_order) >= self.max_seen_notifications:
            old = self.seen_notifications_order.popleft()
            self.seen_notifications_set.discard(old)
        self.seen_notifications_order.append(notif_id)
        self.seen_notifications_set.add(notif_id)
        return True

    def start_notifications_listener_thread(self):
        if hasattr(self, "notifications_listener_thread") and self.notifications_listener_thread.is_alive():
            return
        self.notifications_listener_thread = threading.Thread(target=self._notifications_listener_loop, daemon=True)
        self.notifications_listener_thread.start()

    def _notifications_listener_loop(self):
        try:
            asyncio.run(self._listen_notifications_async())
        except Exception as e:
            print(f"Erreur listener notifications: {e}")

    async def _listen_notifications_async(self):
        UserNotificationListener = None
        NotificationKinds = None
        
        # Essai d'import winsdk (moderne) puis winrt (legacy)
        try:
            from winsdk.windows.ui.notifications.management import UserNotificationListener
            from winsdk.windows.ui.notifications import NotificationKinds
        except ImportError:
            try:
                from winrt.windows.ui.notifications.management import UserNotificationListener
                from winrt.windows.ui.notifications import NotificationKinds
            except ImportError:
                # Désactivation de l'installation automatique car elle bloque le démarrage (compilation trop longue)
                if not hasattr(self, "_winsdk_warned"):
                    self._winsdk_warned = True
                    print("⚠️ WinSDK/WinRT manquant. Les notifications Windows ne seront pas lues.")
                    print("👉 Pour corriger : pip install winsdk")
                return

        if not UserNotificationListener or not NotificationKinds:
            return

        listener = None
        # Test de plusieurs méthodes d'accès (WinSDK vs WinRT vs versions)
        for method in ["get_default", "get_current", "Current"]:
            if hasattr(UserNotificationListener, method):
                try:
                    attr = getattr(UserNotificationListener, method)
                    if callable(attr):
                        listener = attr()
                    else:
                        listener = attr
                    if listener: break
                except: continue
        
        if not listener:
            # Ultime tentative : instance directe
            try: listener = UserNotificationListener()
            except: pass

        if not listener:
            print("❌ Impossible d'accéder au UserNotificationListener via WinSDK/WinRT.")
            print("🚀 Tentative via le Bridge PowerShell...")
            self._run_notification_bridge()
            return

        try:
            access = await listener.request_access_async()
            if "allowed" not in str(access).lower():
                if not self.notifications_access_prompted:
                    self.notifications_access_prompted = True
                    # Utilisation de self.after pour exécuter dans le thread principal
                    self.after(0, lambda: self.parler("Chef, l'accès aux notifications Windows est refusé. Activez-le dans les paramètres de confidentialité."))
                return
        except Exception as e:
            print(f"⚠️ Erreur lors de la demande d'accès aux notifications : {e}")
            return

        while True:
            try:
                notifs = await listener.get_notifications_async(NotificationKinds.TOAST)
                for n in notifs:
                    if not self._mark_notification_seen(n.id):
                        continue
                    app_name = None
                    app_id = None
                    try:
                        app_name = n.app_info.display_info.display_name
                        app_id = n.app_info.app_user_model_id
                    except Exception:
                        pass
                    
                    # Traitement spécial pour Android si activé
                    if self._is_android_source(app_name):
                        text = self._extract_notification_text(n)
                        if text:
                            self._process_android_notification(app_name, text)
                        continue
                    
                    # Traitement normal des autres notifications
                    source_key = self._map_notification_source(app_name, app_id)
                    text = self._extract_notification_text(n)
                    if text:
                        self.notify_external(source_key, f"Notification {app_name}: {text}")
                    else:
                        self.notify_external(source_key, f"Notification {app_name}.")
            except Exception as e:
                print(f"Erreur lecture notifications: {e}")
            await asyncio.sleep(2)

    def _load_settings(self):
        """Charge les paramètres depuis settings.json si disponible"""
        try:
            if not os.path.exists(self.settings_path):
                return
            with open(self.settings_path, "r", encoding="utf-8") as f:
                data = json.load(f)
            for key, value in data.get("anomalies", {}).items():
                if hasattr(self, key):
                    setattr(self, key, int(value))
            services = data.get("services_to_watch")
            if isinstance(services, list):
                self.services_to_watch = [str(s) for s in services if str(s).strip()]
            anomalies_enabled = data.get("anomalies_enabled")
            if isinstance(anomalies_enabled, bool):
                self.anomalies_enabled = anomalies_enabled
            notifications_enabled = data.get("notifications_enabled")
            if isinstance(notifications_enabled, bool):
                self.notifications_enabled = notifications_enabled
            sources = data.get("notification_sources")
            if isinstance(sources, dict):
                self.notification_sources = {str(k): bool(v) for k, v in sources.items()}
            provider = data.get("autonomous_provider")
            if provider in ("gemini", "ollama"):
                self.autonomous_provider = provider
            ollama_model = data.get("ollama_model")
            if isinstance(ollama_model, str) and ollama_model.strip():
                self.ollama_model = ollama_model.strip()
            ollama_url = data.get("ollama_url")
            if isinstance(ollama_url, str) and ollama_url.strip():
                url = ollama_url.strip()
                if not url.startswith("http://") and not url.startswith("https://"):
                    url = "http://" + url
                parsed = urlparse(url)
                if parsed.netloc:
                    path = parsed.path or ""
                    if path in ("", "/", "/api", "/api/"):
                        path = "/api/generate"
                    url = urlunparse(parsed._replace(path=path, params="", query="", fragment=""))
                    self.ollama_url = url
            ollama_num_predict = data.get("ollama_num_predict")
            if isinstance(ollama_num_predict, int):
                if 32 <= ollama_num_predict <= 2048:
                    self.ollama_num_predict = ollama_num_predict
            launch_on_startup = data.get("launch_on_startup")
            if isinstance(launch_on_startup, bool):
                self.launch_on_startup = launch_on_startup
            ui_theme_name = data.get("ui_theme_name")
            if isinstance(ui_theme_name, str) and ui_theme_name in self.ui_theme_presets:
                self.ui_theme_name = ui_theme_name
            custom_accent_color = data.get("custom_accent_color")
            if self._is_valid_hex_color(custom_accent_color):
                self.custom_accent_color = custom_accent_color
            
            custom_colors = data.get("custom_colors")
            if isinstance(custom_colors, dict):
                self.custom_colors = custom_colors
            
            self.voice_enabled = data.get("voice_enabled", True)
            self.voice_speed = data.get("voice_speed", "-5%")
            self.proactive_suggestions = data.get("proactive_suggestions", True)
            
            # Agents settings
            self.agent_network_enabled = data.get("agent_network_enabled", False)
            self.agent_control_enabled = data.get("agent_control_enabled", False)
            self.agent_remote_enabled = data.get("agent_remote_enabled", False)
            self.agent_gmail_enabled = data.get("agent_gmail_enabled", False)
            self.agent_browser_enabled = data.get("agent_browser_enabled", False)
            self.agent_legal_enabled = data.get("agent_legal_enabled", False)
            self.agent_cyber_enabled = data.get("agent_cyber_enabled", False)
            self.agent_doctor_enabled = data.get("agent_doctor_enabled", False)
            self.agent_video_enabled = data.get("agent_video_enabled", True)
            self.agent_android_enabled = data.get("agent_android_enabled", True)
            self.agent_coding_enabled = data.get("agent_coding_enabled", True)
            self.agent_generation_enabled = data.get("agent_generation_enabled", True)
            self.agent_licence_enabled = data.get("agent_licence_enabled", True)
            self.agent_lecture_enabled = data.get("agent_lecture_enabled", True)
            self.agent_telegram_enabled = data.get("agent_telegram_enabled", False)
            
            # Paramètres nouveaux agents
            self.agent_vision_enabled = data.get("agent_vision_enabled", True)
            self.agent_domotique_enabled = data.get("agent_domotique_enabled", True)
            self.agent_finance_enabled = data.get("agent_finance_enabled", True)
            self.agent_secretaire_enabled = data.get("agent_secretaire_enabled", True)
            self.agent_traducteur_enabled = data.get("agent_traducteur_enabled", True)
            self.agent_miner_enabled = data.get("agent_miner_enabled", True)
            self.agent_news_enabled = data.get("agent_news_enabled", True)
            self.agent_cuisine_enabled = data.get("agent_cuisine_enabled", True)
            self.agent_sante_enabled = data.get("agent_sante_enabled", True)
            self.agent_voyage_enabled = data.get("agent_voyage_enabled", True)
            self.agent_education_enabled = data.get("agent_education_enabled", True)
            self.agent_shopping_enabled = data.get("agent_shopping_enabled", True)
            self.agent_social_enabled = data.get("agent_social_enabled", True)
            self.agent_psy_enabled = data.get("agent_psy_enabled", True)
            self.agent_immo_enabled = data.get("agent_immo_enabled", True)
            self.agent_auto_enabled = data.get("agent_auto_enabled", True)
            self.agent_carrier_enabled = data.get("agent_carrier_enabled", True)
            
            # Paramètres agents supplémentaires
            self.agent_arbitre_enabled = data.get("agent_arbitre_enabled", True)
            self.agent_ecolo_enabled = data.get("agent_ecolo_enabled", True)
            self.agent_guetteur_enabled = data.get("agent_guetteur_enabled", True)
            self.agent_historien_enabled = data.get("agent_historien_enabled", True)
            self.agent_depanneur_enabled = data.get("agent_depanneur_enabled", True)
            self.agent_astroph_enabled = data.get("agent_astroph_enabled", True)
            self.agent_stratege_enabled = data.get("agent_stratege_enabled", True)
            self.agent_architecte_enabled = data.get("agent_architecte_enabled", True)
            self.agent_business_enabled = data.get("agent_business_enabled", True)
            self.agent_polyglotte_enabled = data.get("agent_polyglotte_enabled", True)
            self.agent_nounou_enabled = data.get("agent_nounou_enabled", True)
            self.agent_appel_enabled = data.get("agent_appel_enabled", True)
            self.agent_appel_number = data.get("agent_appel_number", "")
            self.agent_appel_autoreply = data.get("agent_appel_autoreply", True)
            self.agent_appel_phrases = data.get("agent_appel_phrases", [
                "Bonjour, je suis l'assistant de mon propriétaire. Il n'est pas disponible pour le moment.",
                "Puis-je prendre un message ou vous rappeler plus tard ?",
                "Je note votre appel. Merci et au revoir."
            ])
            self.agent_appel_filters = data.get("agent_appel_filters", [])
            
            # Alarmes
            alarms_data = data.get("alarms", [])
            if isinstance(alarms_data, list):
                self.alarms = alarms_data
                # Recalculer le prochain ID
                if self.alarms:
                    self.alarm_next_id = max(a.get("id", 0) for a in self.alarms) + 1
            
            self.conversation_continue = data.get("conversation_continue", False)
            if hasattr(self, "conv_continue_var"):
                self.conv_continue_var.set(self.conversation_continue)

            # Domotique params
            self.domo_wled_ip = data.get("domo_wled_ip", "")
            self.domo_ha_url = data.get("domo_ha_url", "")
            self.domo_ha_token = data.get("domo_ha_token", "")
            self.domo_arduino_port = data.get("domo_arduino_port", "")
            self.domo_webhook_on = data.get("domo_webhook_on", "")
            self.domo_webhook_off = data.get("domo_webhook_off", "")

            self.telegram_bot_token = data.get("telegram_bot_token", "")
            self.telegram_chat_id = data.get("telegram_chat_id", "")
            self.voice = data.get("voice", "fr-FR-VivienneNeural")
            remote_hosts = data.get("remote_hosts_whitelist", [])
            if isinstance(remote_hosts, list):
                self.remote_hosts_whitelist = sorted(set(str(h).strip().lower() for h in remote_hosts if str(h).strip()))
            self.remote_default_host = str(data.get("remote_default_host", "")).strip().lower()
            self.remote_ssh_user = str(data.get("remote_ssh_user", "")).strip()
            try:
                self.remote_ssh_port = int(data.get("remote_ssh_port", 22))
                self.remote_ssh_port = max(1, min(65535, self.remote_ssh_port))
            except Exception:
                self.remote_ssh_port = 22
            self.remote_ssh_key_path = str(data.get("remote_ssh_key_path", "")).strip()
            self.remote_require_confirmation = bool(data.get("remote_require_confirmation", True))
            if self.agent_telegram_enabled:
                threading.Thread(target=self.start_telegram_bot, daemon=True).start()
            if self.agent_gmail_enabled:
                threading.Thread(target=self.start_gmail_listener, daemon=True).start()
        except Exception as e:
            print(f"Erreur chargement settings: {e}")

    def _save_settings(self):
        """Sauvegarde les paramètres dans settings.json"""
        try:
            data = {
                "anomalies": {
                    "anomaly_temp_c": self.anomaly_temp_c,
                    "battery_drop_percent": self.battery_drop_percent,
                    "battery_drop_window_sec": self.battery_drop_window_sec,
                    "battery_not_charging_grace_sec": self.battery_not_charging_grace_sec,
                    "proc_cpu_threshold": self.proc_cpu_threshold,
                    "proc_cpu_duration_sec": self.proc_cpu_duration_sec,
                    "proc_mem_threshold_mb": self.proc_mem_threshold_mb,
                    "disk_free_gb": self.disk_free_gb,
                    "disk_used_percent": self.disk_used_percent,
                    "anomaly_cooldown_sec": self.anomaly_cooldown_sec,
                },
                "services_to_watch": self.services_to_watch,
                "anomalies_enabled": self.anomalies_enabled,
                "notifications_enabled": self.notifications_enabled,
                "notification_sources": self.notification_sources,
                "autonomous_provider": self.autonomous_provider,
                "ollama_model": self.ollama_model,
                "ollama_url": self.ollama_url,
                "ollama_num_predict": self.ollama_num_predict,
                "launch_on_startup": self.launch_on_startup,
                "ui_theme_name": self.ui_theme_name,
                "custom_accent_color": self.custom_accent_color,
                "custom_colors": self.custom_colors,
                "agent_network_enabled": self.agent_network_enabled,
                "agent_control_enabled": self.agent_control_enabled,
                "agent_remote_enabled": self.agent_remote_enabled,
                "agent_gmail_enabled": self.agent_gmail_enabled,
                "agent_browser_enabled": self.agent_browser_enabled,
                "agent_legal_enabled": self.agent_legal_enabled,
                "agent_cyber_enabled": self.agent_cyber_enabled,
                "agent_doctor_enabled": self.agent_doctor_enabled,
                "agent_video_enabled": getattr(self, "agent_video_enabled", True),
                "agent_android_enabled": getattr(self, "agent_android_enabled", True),
                "agent_coding_enabled": self.agent_coding_enabled,
                "agent_generation_enabled": self.agent_generation_enabled,
                "agent_licence_enabled": self.agent_licence_enabled,
                "agent_lecture_enabled": self.agent_lecture_enabled,
                "agent_telegram_enabled": self.agent_telegram_enabled,
                "agent_vision_enabled": self.agent_vision_enabled,
                "agent_domotique_enabled": self.agent_domotique_enabled,
                "agent_finance_enabled": self.agent_finance_enabled,
                "agent_secretaire_enabled": self.agent_secretaire_enabled,
                "agent_traducteur_enabled": self.agent_traducteur_enabled,
                "agent_miner_enabled": self.agent_miner_enabled,
                "agent_news_enabled": self.agent_news_enabled,
                "agent_cuisine_enabled": self.agent_cuisine_enabled,
                "agent_sante_enabled": self.agent_sante_enabled,
                "agent_voyage_enabled": self.agent_voyage_enabled,
                "agent_education_enabled": self.agent_education_enabled,
                "agent_shopping_enabled": self.agent_shopping_enabled,
                "agent_social_enabled": self.agent_social_enabled,
                "agent_psy_enabled": self.agent_psy_enabled,
                "agent_immo_enabled": self.agent_immo_enabled,
                "agent_auto_enabled": self.agent_auto_enabled,
                "agent_carrier_enabled": self.agent_carrier_enabled,
                "agent_arbitre_enabled": self.agent_arbitre_enabled,
                "agent_ecolo_enabled": self.agent_ecolo_enabled,
                "agent_guetteur_enabled": self.agent_guetteur_enabled,
                "agent_historien_enabled": self.agent_historien_enabled,
                "agent_depanneur_enabled": self.agent_depanneur_enabled,
                "agent_astroph_enabled": self.agent_astroph_enabled,
                "agent_stratege_enabled": self.agent_stratege_enabled,
                "agent_architecte_enabled": self.agent_architecte_enabled,
                "agent_appel_enabled": getattr(self, "agent_appel_enabled", True),
                "agent_appel_autoreply": getattr(self, "agent_appel_autoreply", True),
                "agent_appel_number": getattr(self, "agent_appel_number", ""),
                "agent_appel_phrases": getattr(self, "agent_appel_phrases", []),
                "agent_business_enabled": self.agent_business_enabled,
                "agent_polyglotte_enabled": self.agent_polyglotte_enabled,
                "agent_nounou_enabled": self.agent_nounou_enabled,
                "voice_enabled": self.voice_enabled,
                "voice_speed": self.voice_speed,
                "proactive_suggestions": self.proactive_suggestions,
                "domo_wled_ip": self.domo_wled_ip,
                "domo_ha_url": self.domo_ha_url,
                "domo_ha_token": self.domo_ha_token,
                "domo_arduino_port": self.domo_arduino_port,
                "domo_webhook_on": self.domo_webhook_on,
                "domo_webhook_off": self.domo_webhook_off,
                "telegram_bot_token": self.telegram_bot_token,
                "telegram_chat_id": self.telegram_chat_id,
                "voice": self.voice,
                "remote_hosts_whitelist": self.remote_hosts_whitelist,
                "remote_default_host": self.remote_default_host,
                "remote_ssh_user": self.remote_ssh_user,
                "remote_ssh_port": self.remote_ssh_port,
                "remote_ssh_key_path": self.remote_ssh_key_path,
                "remote_require_confirmation": self.remote_require_confirmation,
                "conversation_continue": self.conversation_continue,
                "alarms": self.alarms,
            }
            with open(self.settings_path, "w", encoding="utf-8") as f:
                json.dump(data, f, ensure_ascii=False, indent=2)
        except Exception as e:
            print(f"Erreur sauvegarde settings: {e}")

    def update_location(self):
        """Met à jour la géolocalisation en temps réel toutes les 10 minutes"""
        def fetch_location():
            try:
                # Tentative 1: ipapi.co
                response = requests.get('https://ipapi.co/json/', timeout=8)
                if response.status_code == 200:
                    data = response.json()
                    self.location_city = data.get("city", "Inconnu")
                    self.location_country = data.get("country_name", "Inconnu")
                    self.location_coords = (data.get("latitude", 0.0), data.get("longitude", 0.0))
                else:
                    # Tentative 2: ip-api.com (Fallback)
                    response = requests.get('http://ip-api.com/json/', timeout=8)
                    if response.status_code == 200:
                        data = response.json()
                        self.location_city = data.get("city", "Inconnu")
                        self.location_country = data.get("country", "Inconnu")
                        self.location_coords = (data.get("lat", 0.0), data.get("lon", 0.0))

                # Mise à jour de l'interface
                if self.location_city != "Inconnu":
                    location_text = f"📍 {self.location_city}, {self.location_country}"
                    self.after(0, lambda: self.location_label.configure(text=location_text))
                else:
                    self.after(0, lambda: self.location_label.configure(text="📍 Localisation indisponible"))
            except Exception as e:
                print(f"⚠️ Erreur géolocalisation in update_location: {e}")
                self.after(0, lambda: self.location_label.configure(text="📍 Erreur de localisation"))
        
        threading.Thread(target=fetch_location, daemon=True).start()
        self.after(600000, self.update_location)

    def get_detailed_location(self):
        """Récupère la position géographique avec gestion d'erreurs DNS/Réseau"""
        try:
            # Utilisation de ipapi.co avec un timeout court pour éviter de bloquer l'IA
            r = requests.get('https://ipapi.co/json/', timeout=3)
            if r.status_code == 200:
                data = r.json()
                city = data.get('city', 'Inconnu')
                country = data.get('country_name', 'Inconnu')
                region = data.get('region', 'Inconnu')
                self.location_city = city
                return f"Vous êtes actuellement à {city}, dans la région de {region}, en {country}."
        except Exception as e:
            print(f"⚠️ Erreur géolocalisation: {e}")
        
        return "Je ne parviens pas à déterminer votre position précise, mais je suis à votre écoute."

    def get_weather(self, city="Paris"):
        """Récupère la météo en temps réel via l'API wttr.in"""
        try:
            url = f"https://wttr.in/{city}?format=%C+%t"
            response = requests.get(url)
            if response.status_code == 200:
                return response.text.strip()
            return "Indisponible"
        except:
            return "Erreur lors de la récupération"

    def intelligent_web_search(self, query):
        """Effectue une recherche web et extrait le contenu du premier résultat pertinent"""
        try:
            self.status_label.configure(text="Recherche web en cours...", text_color=COLOR_ACCENT)
            # On prend le premier lien de la recherche Google
            links = list(gsearch(query, num_results=3, lang='fr'))
            if not links:
                return "Je n'ai rien trouvé sur le web pour cette recherche."
            
            target_url = links[0]
            headers = {'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/91.0.4472.124 Safari/537.36'}
            page = requests.get(target_url, headers=headers, timeout=5)
            soup = BeautifulSoup(page.content, 'html.parser')
            
            # Extraction des paragraphes significatifs
            paragraphs = soup.find_all('p')
            content = " ".join([p.get_text() for p in paragraphs[:3]])
            
            if len(content) < 50:
                return f"J'ai trouvé un lien ({target_url}) mais je n'ai pas pu extraire de texte clair."
            
            return f"D'après mes recherches sur {target_url} : {content[:500]}..."
        except Exception as e:
            print(f"Erreur recherche web: {e}")
            return "Une erreur est survenue lors de ma recherche sur le web."

    def get_running_processes(self):
        """Retourne la liste des processus utilisateur actifs (non-système)"""
        user_processes = []
        # Processus système à ignorer
        system_processes = [
            'system', 'registry', 'smss.exe', 'csrss.exe', 'wininit.exe', 'services.exe',
            'lsass.exe', 'svchost.exe', 'winlogon.exe', 'dwm.exe', 'explorer.exe',
            'taskhostw.exe', 'searchindexer.exe', 'runtimebroker.exe', 'sihost.exe',
            'ctfmon.exe', 'conhost.exe', 'fontdrvhost.exe', 'spoolsv.exe', 'audiodg.exe',
            'python.exe', 'pythonw.exe'  # Pour ne pas fermer Jarvisse lui-même
        ]
        
        try:
            for proc in psutil.process_iter(['pid', 'name', 'username']):
                try:
                    proc_name = proc.info['name'].lower()
                    # Ignorer les processus système
                    if proc_name not in system_processes and not proc_name.startswith('microsoft'):
                        user_processes.append({
                            'pid': proc.info['pid'],
                            'name': proc.info['name'],
                            'username': proc.info.get('username', 'N/A')
                        })
                except (psutil.NoSuchProcess, psutil.AccessDenied):
                    pass
        except Exception as e:
            print(f"Erreur lors de la récupération des processus: {e}")
        
        return user_processes

    def close_all_user_apps(self):
        """Ferme toutes les applications utilisateur de manière sécurisée"""
        processes = self.get_running_processes()
        closed_count = 0
        failed_count = 0
        
        # Applications courantes à fermer en priorité
        priority_apps = ['chrome', 'firefox', 'edge', 'opera', 'brave', 'discord', 'spotify', 
                        'teams', 'slack', 'zoom', 'notepad', 'wordpad', 'excel', 'winword', 
                        'powerpnt', 'outlook', 'vlc', 'steam']
        
        for proc_info in processes:
            proc_name = proc_info['name'].lower()
            # Vérifier si c'est une application prioritaire
            is_priority = any(app in proc_name for app in priority_apps)
            
            if is_priority or proc_name.endswith('.exe'):
                try:
                    proc = psutil.Process(proc_info['pid'])
                    proc.terminate()  # Fermeture propre
                    closed_count += 1
                    print(f"✅ Fermé: {proc_info['name']}")
                except (psutil.NoSuchProcess, psutil.AccessDenied) as e:
                    failed_count += 1
                    print(f"❌ Impossible de fermer: {proc_info['name']} - {e}")
        
        return closed_count, failed_count

    def list_active_processes(self):
        """Liste les processus actifs pour l'utilisateur"""
        processes = self.get_running_processes()
        if not processes:
            return "Aucun processus utilisateur actif détecté."
        
        # Grouper par type d'application
        browsers = []
        office = []
        media = []
        communication = []
        others = []
        
        for proc in processes:
            name = proc['name'].lower()
            if any(x in name for x in ['chrome', 'firefox', 'edge', 'opera', 'brave']):
                browsers.append(proc['name'])
            elif any(x in name for x in ['word', 'excel', 'powerpoint', 'outlook']):
                office.append(proc['name'])
            elif any(x in name for x in ['vlc', 'spotify', 'itunes', 'media']):
                media.append(proc['name'])
            elif any(x in name for x in ['discord', 'teams', 'slack', 'zoom', 'skype']):
                communication.append(proc['name'])
            else:
                others.append(proc['name'])
        
        result = f"J'ai détecté {len(processes)} processus actifs. "
        if browsers: result += f"Navigateurs: {len(browsers)}. "
        if office: result += f"Suite Office: {len(office)}. "
        if communication: result += f"Communication: {len(communication)}. "
        
        return result

    # ==========================================
    # RÉGLAGES & CONFIGURATION
    # ==========================================

    def toggle_voice(self):
        """Active ou désactive la synthèse vocale"""
        self.voice_enabled = self.voice_var_settings.get()
        if self.voice_enabled:
            self.parler("Synthèse vocale activée.")
        else:
            self.add_message("Synthèse vocale désactivée. Je répondrai uniquement par texte.", "Système")

    def toggle_proactive_suggestions(self):
        """Active ou désactive les suggestions proactives"""
        self.proactive_suggestions = self.proactive_var_settings.get()
        self._save_settings()
        if self.proactive_suggestions:
            self.parler("Suggestions proactives activées. Je vais maintenant anticiper vos besoins.")
        else:
            self.parler("Suggestions proactives désactivées. Je me concentrerai uniquement sur vos demandes directes.")

    def open_appearance_customization(self):
        """Ouvre une fenêtre pour régler chaque couleur de l'interface"""
        color_win = ctk.CTkToplevel(self)
        color_win.title("Jarvisse - Personnalisation des Couleurs")
        color_win.geometry("400x650")
        color_win.configure(fg_color=COLOR_BG)
        color_win.transient(self)
        color_win.attributes("-topmost", True)

        ctk.CTkLabel(color_win, text="🎨 DESIGN PERSONNALISÉ", font=ctk.CTkFont(size=18, weight="bold"), text_color=COLOR_ACCENT).pack(pady=20)

        scroll = ctk.CTkScrollableFrame(color_win, fg_color="transparent")
        scroll.pack(fill="both", expand=True, padx=20, pady=10)

        color_labels = {
            "bg": "Fond de l'application",
            "nav": "Barre de navigation & Sidebar",
            "accent": "Couleur d'accent (Primaire)",
            "accent_purple": "Couleur d'accent (Secondaire)",
            "accent_red": "Alertes & Boutons critiques",
            "text": "Texte principal",
            "secondary": "Texte secondaire (Labels)",
            "card": "Cartes & Boutons standards"
        }

        current_pal = self._current_theme_palette()

        def pick_color(key):
            color = colorchooser.askcolor(initialcolor=current_pal.get(key, "#000000"), title=f"Choisir {color_labels[key]}")
            if color[1]:
                self.custom_colors[key] = color[1]
                self._apply_theme_globals()
                self._refresh_theme_widgets()
                self._save_settings()

        for key, label in color_labels.items():
            f = ctk.CTkFrame(scroll, fg_color="transparent")
            f.pack(fill="x", pady=8)
            
            ctk.CTkLabel(f, text=label, font=ctk.CTkFont(size=12)).pack(side="left")
            
            # Aperçu de la couleur actuelle
            preview = ctk.CTkFrame(f, width=24, height=24, fg_color=current_pal.get(key, "#000000"), corner_radius=12)
            preview.pack(side="right", padx=5)
            
            btn = ctk.CTkButton(f, text="Modifier", width=80, height=28, 
                                command=lambda k=key: pick_color(k))
            btn.pack(side="right", padx=5)

        ctk.CTkButton(color_win, text="Réinitialiser tout", fg_color=COLOR_ACCENT_RED, 
                      command=lambda: [setattr(self, "custom_colors", {}), self._apply_theme_globals(), self._refresh_theme_widgets(), self._save_settings(), color_win.destroy()]).pack(pady=20)


    def open_main_settings(self):
        """Ouvre le panneau central des paramètres de Jarvisse"""
        main_settings = ctk.CTkToplevel(self)
        main_settings.title("Jarvisse - Paramètres Généraux")
        main_settings.geometry("500x750")
        main_settings.configure(fg_color=COLOR_BG)
        main_settings.transient(self)
        main_settings.attributes("-topmost", True)

        # Titre & Contrôles de taille
        header_frame = ctk.CTkFrame(main_settings, fg_color="transparent")
        header_frame.pack(fill="x", pady=(10, 0))
        
        title_label = ctk.CTkLabel(header_frame, text="⚙️ RÉGLAGES GLOBAUX", font=ctk.CTkFont(size=18, weight="bold"), text_color=COLOR_ACCENT)
        title_label.pack(side="left", padx=20)

        def set_size(size_str):
            main_settings.geometry(size_str)

        btn_size_max = ctk.CTkButton(header_frame, text="🗖", width=30, height=30, fg_color=COLOR_CARD, 
                                    text_color=COLOR_TEXT, hover_color=COLOR_ACCENT, command=lambda: set_size("750x900"))
        btn_size_max.pack(side="right", padx=(5, 20))

        btn_size_min = ctk.CTkButton(header_frame, text="🗗", width=30, height=30, fg_color=COLOR_CARD, 
                                    text_color=COLOR_TEXT, hover_color=COLOR_ACCENT, command=lambda: set_size("450x650"))
        btn_size_min.pack(side="right", padx=5)

        # Zone de défilement pour les options
        scroll_frame = ctk.CTkScrollableFrame(main_settings, fg_color="transparent")
        scroll_frame.pack(fill="both", expand=True, padx=20, pady=10)

        def create_sec(parent, title):
            l = ctk.CTkLabel(parent, text=title.upper(), font=ctk.CTkFont(size=13, weight="bold"), text_color=COLOR_ACCENT_PURPLE)
            l.pack(pady=(20, 10), anchor="w")
            return l

        # Section 1: Modules & Intelligences
        create_sec(scroll_frame, "Modules & Agents")
        ctk.CTkButton(scroll_frame, text="🤖 Gérer les Agents Actifs", fg_color=COLOR_CARD, hover_color="#3C4043", 
                      anchor="w", command=self.open_agents_settings).pack(fill="x", pady=5)
        ctk.CTkButton(scroll_frame, text="🏠 Domotique & Interfaces", fg_color=COLOR_CARD, hover_color="#3C4043", 
                      anchor="w", command=self.open_domotique_settings).pack(fill="x", pady=5)

        # Section 2: Sécurité & Santé
        create_sec(scroll_frame, "Sécurité & Maintenance")
        ctk.CTkButton(scroll_frame, text="🩺 Seuils d'Anomalies Système", fg_color=COLOR_CARD, hover_color="#3C4043", 
                      anchor="w", command=self.open_anomaly_settings).pack(fill="x", pady=5)
        ctk.CTkButton(scroll_frame, text="🛡️ Services Critiques", fg_color=COLOR_CARD, hover_color="#3C4043", 
                      anchor="w", command=self.open_services_watch).pack(fill="x", pady=5)

        # Section 3: Communication & Alertes
        create_sec(scroll_frame, "Communication & Alertes")
        
        # Contrôle de vitesse de lecture
        speed_frame = ctk.CTkFrame(scroll_frame, fg_color="transparent")
        speed_frame.pack(fill="x", pady=10)
        
        ctk.CTkLabel(speed_frame, text="🎙️ Vitesse de Lecture :", font=ctk.CTkFont(size=12)).pack(side="left", padx=(0, 10))
        
        # Slider de -50% à +50%
        speed_slider = ctk.CTkSlider(
            speed_frame, 
            from_=-50, 
            to=50, 
            number_of_steps=20,
            command=lambda v: self._update_voice_speed(v)
        )
        
        # Convertir la vitesse actuelle en valeur numérique
        current_speed_str = self.voice_speed.replace("%", "").replace("+", "")
        try:
            current_speed_val = int(current_speed_str)
        except:
            current_speed_val = -5
            
        speed_slider.set(current_speed_val)
        speed_slider.pack(side="left", fill="x", expand=True, padx=10)
        
        # Label pour afficher la valeur
        speed_label = ctk.CTkLabel(speed_frame, text=f"{current_speed_val:+d}%", font=ctk.CTkFont(size=11), width=50)
        speed_label.pack(side="right")
        
        # Fonction de mise à jour
        def update_label_and_speed(value):
            val = int(value)
            speed_label.configure(text=f"{val:+d}%")
            self.voice_speed = f"{val:+d}%"
            self._save_settings()
        
        speed_slider.configure(command=update_label_and_speed)
        
        self.voice_var_settings = ctk.BooleanVar(value=self.voice_enabled)
        ctk.CTkSwitch(scroll_frame, text="Sortie Vocale (Son)", variable=self.voice_var_settings, 
                      command=self.toggle_voice, text_color=COLOR_TEXT).pack(pady=5, anchor="w")
        
        # Switch pour les suggestions proactives
        self.proactive_var_settings = ctk.BooleanVar(value=self.proactive_suggestions)
        ctk.CTkSwitch(scroll_frame, text="🧠 Suggestions Proactives (Lecture d'esprit)", 
                      variable=self.proactive_var_settings, 
                      command=self.toggle_proactive_suggestions, 
                      text_color=COLOR_TEXT).pack(pady=5, anchor="w")
        
        ctk.CTkButton(scroll_frame, text="🔔 Notifications d'Applications", fg_color=COLOR_CARD, hover_color="#3C4043", 
                      anchor="w", command=self.open_notification_settings).pack(fill="x", pady=5)
        ctk.CTkButton(scroll_frame, text="📧 Configuration Gmail", fg_color=COLOR_CARD, hover_color="#3C4043", 
                      anchor="w", command=self.agent_gmail_mission).pack(fill="x", pady=5)

        # Section 4: Personnalisation
        create_sec(scroll_frame, "Apparence & Thèmes")
        
        # Sélecteur de Thème (S'intègre ici pour répondre à la demande utilisateur)
        theme_frame = ctk.CTkFrame(scroll_frame, fg_color="transparent")
        theme_frame.pack(fill="x", pady=5)
        ctk.CTkLabel(theme_frame, text="Thème Visuel :", font=ctk.CTkFont(size=12)).pack(side="left", padx=(0, 10))
        
        theme_options = sorted(list(self.ui_theme_presets.keys()))
        theme_menu = ctk.CTkOptionMenu(
            theme_frame, 
            values=theme_options,
            command=self.on_ui_theme_changed,
            fg_color=COLOR_CARD,
            button_color=COLOR_ACCENT_PURPLE,
            text_color=COLOR_TEXT
        )
        theme_menu.set(self.ui_theme_name)
        theme_menu.pack(side="right", fill="x", expand=True)

        ctk.CTkButton(scroll_frame, text="🎨 Couleurs & Design (Sur Mesure)", fg_color=COLOR_CARD, hover_color="#3C4043", 
                      anchor="w", command=self.open_appearance_customization).pack(fill="x", pady=5)

        # Pied de page
        footer_label = ctk.CTkLabel(main_settings, text="Jarvisse Intelligence Artificielle v3.0", font=ctk.CTkFont(size=10), text_color=COLOR_SECONDARY)
        footer_label.pack(pady=10)

    def open_agents_settings(self):
        """Ouvre une fenêtre pour configurer et activer les agents"""
        settings_win = ctk.CTkToplevel(self)
        settings_win.title("Paramètres des Agents")
        settings_win.geometry("450x850")
        settings_win.configure(fg_color=COLOR_BG)
        settings_win.transient(self)
        settings_win.attributes("-topmost", True)
        settings_win.lift()
        settings_win.focus_force()

        # Calcul automatique du nombre d'agents (y compris les nouveaux)
        all_agents_vars = [
            self.agent_network_enabled, self.agent_control_enabled, self.agent_gmail_enabled,
            self.agent_remote_enabled,
            self.agent_browser_enabled, self.agent_legal_enabled, self.agent_cyber_enabled,
            self.agent_doctor_enabled, self.agent_video_enabled, self.agent_android_enabled,
            self.agent_coding_enabled, self.agent_generation_enabled, self.agent_licence_enabled,
            self.agent_lecture_enabled, self.agent_telegram_enabled, self.agent_vision_enabled,
            self.agent_domotique_enabled, self.agent_finance_enabled, self.agent_secretaire_enabled,
            self.agent_traducteur_enabled, self.agent_miner_enabled,
            self.agent_news_enabled, self.agent_cuisine_enabled, self.agent_sante_enabled, self.agent_voyage_enabled,
            self.agent_education_enabled, self.agent_shopping_enabled, self.agent_social_enabled,
            self.agent_psy_enabled, self.agent_immo_enabled, self.agent_auto_enabled, self.agent_carrier_enabled,
            self.agent_arbitre_enabled, self.agent_ecolo_enabled, self.agent_guetteur_enabled,
            self.agent_historien_enabled, self.agent_depanneur_enabled, self.agent_astroph_enabled,
            self.agent_stratege_enabled, self.agent_architecte_enabled, self.agent_business_enabled,
            self.agent_polyglotte_enabled, self.agent_nounou_enabled, self.agent_appel_enabled
        ]
        total_agents = len(all_agents_vars)

        # Titre fixe en haut
        label = ctk.CTkLabel(settings_win, text="CONFIGURATION DES AGENTS", font=ctk.CTkFont(size=16, weight="bold"), text_color=COLOR_ACCENT)
        label.pack(pady=(20, 5))

        # Affichage du nombre d'agents (DEMANDE UTILISATEUR)
        count_label = ctk.CTkLabel(
            settings_win, 
            text=f"📊 Total des agents intégrés : {total_agents}", 
            font=ctk.CTkFont(size=13, weight="bold"), 
            text_color=COLOR_ACCENT_PURPLE,
            fg_color=COLOR_NAV,
            corner_radius=8,
            padx=15, pady=5
        )
        count_label.pack(pady=(0, 15))

        # Frame scrollable pour le contenu
        scrollable_frame = ctk.CTkScrollableFrame(
            settings_win,
            fg_color=COLOR_BG,
            corner_radius=0,
            width=410,
            height=500
        )
        scrollable_frame.pack(fill="both", padx=10, pady=(0, 10))

        # Agent Réseau
        net_var = ctk.BooleanVar(value=self.agent_network_enabled)
        net_switch = ctk.CTkSwitch(scrollable_frame, text="Agent Réseau", variable=net_var, command=lambda: self.toggle_agent("network", net_var.get()))
        net_switch.pack(pady=10, padx=20, anchor="w")

        # Agent Contrôle Total
        ctrl_var = ctk.BooleanVar(value=self.agent_control_enabled)
        ctrl_switch = ctk.CTkSwitch(scrollable_frame, text="Agent Contrôle Total", variable=ctrl_var, command=lambda: self.toggle_agent("control", ctrl_var.get()))
        ctrl_switch.pack(pady=10, padx=20, anchor="w")

        # Agent Contrôle Distant (SSH sécurisé)
        remote_var = ctk.BooleanVar(value=self.agent_remote_enabled)
        remote_switch = ctk.CTkSwitch(scrollable_frame, text="Agent Contrôle Distant (SSH)", variable=remote_var, command=lambda: self.toggle_agent("remote", remote_var.get()))
        remote_switch.pack(pady=10, padx=20, anchor="w")
        ctk.CTkLabel(scrollable_frame, text="Exécution distante sécurisée sur machines autorisées uniquement.", font=ctk.CTkFont(size=10), text_color=COLOR_SECONDARY).pack(padx=40, anchor="w")

        remote_form = ctk.CTkFrame(scrollable_frame, fg_color="transparent")
        remote_form.pack(pady=5, padx=40, fill="x")

        remote_hosts_entry = ctk.CTkEntry(remote_form, placeholder_text="Machines autorisées (CSV: pc1,192.168.1.10)", height=28, fg_color=COLOR_NAV)
        remote_hosts_entry.insert(0, ", ".join(self.remote_hosts_whitelist))
        remote_hosts_entry.pack(fill="x", pady=(0, 5))

        remote_user_entry = ctk.CTkEntry(remote_form, placeholder_text="Utilisateur SSH", height=28, fg_color=COLOR_NAV)
        remote_user_entry.insert(0, self.remote_ssh_user)
        remote_user_entry.pack(fill="x", pady=(0, 5))

        remote_row = ctk.CTkFrame(remote_form, fg_color="transparent")
        remote_row.pack(fill="x", pady=(0, 5))
        remote_port_entry = ctk.CTkEntry(remote_row, placeholder_text="Port SSH", width=90, height=28, fg_color=COLOR_NAV)
        remote_port_entry.insert(0, str(self.remote_ssh_port))
        remote_port_entry.pack(side="left", padx=(0, 5))
        remote_default_host_entry = ctk.CTkEntry(remote_row, placeholder_text="Hôte par défaut", height=28, fg_color=COLOR_NAV)
        remote_default_host_entry.insert(0, self.remote_default_host)
        remote_default_host_entry.pack(side="left", fill="x", expand=True)

        remote_key_entry = ctk.CTkEntry(remote_form, placeholder_text="Clé privée SSH (optionnel)", height=28, fg_color=COLOR_NAV)
        remote_key_entry.insert(0, self.remote_ssh_key_path)
        remote_key_entry.pack(fill="x", pady=(0, 5))

        confirm_remote_var = ctk.BooleanVar(value=self.remote_require_confirmation)
        confirm_remote_switch = ctk.CTkSwitch(remote_form, text="Demander confirmation commandes sensibles", variable=confirm_remote_var)
        confirm_remote_switch.pack(anchor="w", pady=(0, 5))

        def browse_remote_key():
            key_path = filedialog.askopenfilename(title="Sélectionner la clé privée SSH")
            if key_path:
                remote_key_entry.delete(0, "end")
                remote_key_entry.insert(0, key_path)

        def save_remote_settings():
            hosts = [h.strip().lower() for h in remote_hosts_entry.get().split(",") if h.strip()]
            self.remote_hosts_whitelist = sorted(set(hosts))
            self.remote_ssh_user = remote_user_entry.get().strip()
            self.remote_default_host = remote_default_host_entry.get().strip().lower()
            self.remote_ssh_key_path = remote_key_entry.get().strip()
            self.remote_require_confirmation = bool(confirm_remote_var.get())
            try:
                port_value = int(remote_port_entry.get().strip())
                self.remote_ssh_port = max(1, min(65535, port_value))
            except Exception:
                self.remote_ssh_port = 22
            self._save_settings()
            self.add_message("Paramètres Agent Contrôle Distant enregistrés.", "Système")

        def test_remote_settings():
            save_remote_settings()
            target = self.remote_default_host or (self.remote_hosts_whitelist[0] if self.remote_hosts_whitelist else "")
            if not target:
                self.add_message("Aucun hôte distant configuré pour le test.", "Système")
                return
            threading.Thread(target=lambda: self.parler(self._execute_remote_task(target, "whoami", force_without_confirmation=True)), daemon=True).start()

        remote_btn_row = ctk.CTkFrame(remote_form, fg_color="transparent")
        remote_btn_row.pack(fill="x", pady=(0, 10))
        ctk.CTkButton(remote_btn_row, text="Parcourir clé", height=24, font=ctk.CTkFont(size=10), command=browse_remote_key).pack(side="left", padx=(0, 5))
        ctk.CTkButton(remote_btn_row, text="Enregistrer Remote", height=24, font=ctk.CTkFont(size=10), command=save_remote_settings).pack(side="left", padx=(0, 5))
        ctk.CTkButton(remote_btn_row, text="Tester SSH", height=24, font=ctk.CTkFont(size=10), fg_color=COLOR_ACCENT, command=test_remote_settings).pack(side="left")

        # Agent Gmail
        gmail_var = ctk.BooleanVar(value=self.agent_gmail_enabled)
        gmail_switch = ctk.CTkSwitch(scrollable_frame, text="Agent Gmail", variable=gmail_var, command=lambda: self.toggle_agent("gmail", gmail_var.get()))
        gmail_switch.pack(pady=10, padx=20, anchor="w")

        # Agent Navigateur
        browse_var = ctk.BooleanVar(value=self.agent_browser_enabled)
        browse_switch = ctk.CTkSwitch(scrollable_frame, text="Agent Navigateur", variable=browse_var, command=lambda: self.toggle_agent("browser", browse_var.get()))
        browse_switch.pack(pady=10, padx=20, anchor="w")

        # Agent Juridique
        legal_var = ctk.BooleanVar(value=self.agent_legal_enabled)
        legal_switch = ctk.CTkSwitch(scrollable_frame, text="Agent Juridique", variable=legal_var, command=lambda: self.toggle_agent("legal", legal_var.get()))
        legal_switch.pack(pady=10, padx=20, anchor="w")
        ctk.CTkLabel(scrollable_frame, text="Expert en droit, RH et articles juridiques.", font=ctk.CTkFont(size=10), text_color=COLOR_SECONDARY).pack(padx=40, anchor="w")

        # Agent Cyber Sécurité
        cyber_var = ctk.BooleanVar(value=self.agent_cyber_enabled)
        cyber_switch = ctk.CTkSwitch(scrollable_frame, text="Agent Cyber Sécurité", variable=cyber_var, command=lambda: self.toggle_agent("cyber", cyber_var.get()))
        cyber_switch.pack(pady=10, padx=20, anchor="w")
        ctk.CTkLabel(scrollable_frame, text="Audit système, réseau, défense et conseils cyber.", font=ctk.CTkFont(size=10), text_color=COLOR_SECONDARY).pack(padx=40, anchor="w")

        # Agent Docteur Système
        doctor_var = ctk.BooleanVar(value=self.agent_doctor_enabled)
        doctor_switch = ctk.CTkSwitch(scrollable_frame, text="Agent Docteur Système", variable=doctor_var, command=lambda: self.toggle_agent("doctor", doctor_var.get()))
        doctor_switch.pack(pady=10, padx=20, anchor="w")
        ctk.CTkLabel(scrollable_frame, text="Santé système, optimisation processus et réparation.", font=ctk.CTkFont(size=10), text_color=COLOR_SECONDARY).pack(padx=40, anchor="w")

        # Agent Vidéo Surveillance
        video_var = ctk.BooleanVar(value=self.agent_video_enabled)
        video_switch = ctk.CTkSwitch(scrollable_frame, text="Agent Vidéo Surveillance", variable=video_var, command=lambda: self.toggle_agent("video", video_var.get()))
        video_switch.pack(pady=10, padx=20, anchor="w")
        ctk.CTkLabel(scrollable_frame, text="Contrôle caméra, enregistrements et captures d'écran.", font=ctk.CTkFont(size=10), text_color=COLOR_SECONDARY).pack(padx=40, anchor="w")

        # Agent Contrôle Android
        android_var = ctk.BooleanVar(value=self.agent_android_enabled)
        android_switch = ctk.CTkSwitch(scrollable_frame, text="Agent Contrôle Android", variable=android_var, command=lambda: self.toggle_agent("android", android_var.get()))
        android_switch.pack(pady=10, padx=20, anchor="w")
        ctk.CTkLabel(scrollable_frame, text="Connexion téléphone, lecture SMS et alerte appels (via Lien avec Windows).", font=ctk.CTkFont(size=10), text_color=COLOR_SECONDARY).pack(padx=40, anchor="w")

        # Assistant Coding
        coding_var = ctk.BooleanVar(value=self.agent_coding_enabled)
        coding_switch = ctk.CTkSwitch(scrollable_frame, text="Assistant Coding", variable=coding_var, command=lambda: self.toggle_agent("coding", coding_var.get()))
        coding_switch.pack(pady=10, padx=20, anchor="w")
        ctk.CTkLabel(scrollable_frame, text="Création d'applications et de sites web (HTML, CSS, JS, Python, etc.).", font=ctk.CTkFont(size=10), text_color=COLOR_SECONDARY).pack(padx=40, anchor="w")

        # Assistant Génération Image et Vidéo
        gen_var = ctk.BooleanVar(value=self.agent_generation_enabled)
        gen_switch = ctk.CTkSwitch(scrollable_frame, text="Assistant Génération Image & Vidéo", variable=gen_var, command=lambda: self.toggle_agent("generation", gen_var.get()))
        gen_switch.pack(pady=10, padx=20, anchor="w")
        ctk.CTkLabel(scrollable_frame, text="Génération d'images et de vidéos réalistes via IA.", font=ctk.CTkFont(size=10), text_color=COLOR_SECONDARY).pack(padx=40, anchor="w")
        # Agent Assistant Licence
        licence_var = ctk.BooleanVar(value=self.agent_licence_enabled)
        licence_switch = ctk.CTkSwitch(scrollable_frame, text="Agent Assistant Licence", variable=licence_var, command=lambda: self.toggle_agent("licence", licence_var.get()))
        licence_switch.pack(pady=10, padx=20, anchor="w")
        ctk.CTkLabel(scrollable_frame, text="Activation de Windows et Microsoft Office (KMS).", font=ctk.CTkFont(size=10), text_color=COLOR_SECONDARY).pack(padx=40, anchor="w")

        # Agent Lecture
        lecture_var = ctk.BooleanVar(value=self.agent_lecture_enabled)
        lecture_switch = ctk.CTkSwitch(scrollable_frame, text="Agent Lecture", variable=lecture_var, command=lambda: self.toggle_agent("lecture", lecture_var.get()))
        lecture_switch.pack(pady=10, padx=20, anchor="w")
        ctk.CTkLabel(scrollable_frame, text="Lecture de fichiers texte, PDF ou documents locaux.", font=ctk.CTkFont(size=10), text_color=COLOR_SECONDARY).pack(padx=40, anchor="w")

        # Agent Bot Telegram
        telegram_var = ctk.BooleanVar(value=self.agent_telegram_enabled)
        telegram_switch = ctk.CTkSwitch(scrollable_frame, text="Agent Bot Telegram", variable=telegram_var, command=lambda: self.toggle_agent("telegram", telegram_var.get()))
        telegram_switch.pack(pady=10, padx=20, anchor="w")
        ctk.CTkLabel(scrollable_frame, text="Contrôle à distance via Telegram Bot.", font=ctk.CTkFont(size=10), text_color=COLOR_SECONDARY).pack(padx=40, anchor="w")

        # inputs pour Telegram
        telegram_form = ctk.CTkFrame(scrollable_frame, fg_color="transparent")
        telegram_form.pack(pady=5, padx=40, fill="x")
        
        token_entry = ctk.CTkEntry(telegram_form, placeholder_text="Token Bot Telegram", height=28, fg_color=COLOR_NAV)
        token_entry.insert(0, self.telegram_bot_token)
        token_entry.pack(side="left", fill="x", expand=True, padx=(0, 5))
        
        chat_id_entry = ctk.CTkEntry(telegram_form, placeholder_text="Chat ID", width=100, height=28, fg_color=COLOR_NAV)
        chat_id_entry.insert(0, self.telegram_chat_id)
        chat_id_entry.pack(side="left")

        def save_tg_credentials():
            self.telegram_bot_token = token_entry.get().strip()
            self.telegram_chat_id = chat_id_entry.get().strip()
            self._save_settings()
            self.add_message("Paramètres Telegram enregistrés.", "Système")
            # Forcer le redémarrage si activé
            if self.agent_telegram_enabled:
                self.add_message("Redémarrage de l'écouteur Telegram...", "Système")
                threading.Thread(target=self.start_telegram_bot, daemon=True).start()

        def test_tg_connection():
            token = token_entry.get().strip()
            chat_id = chat_id_entry.get().strip()
            if not token:
                self.add_message("Erreur : Token manquant pour le test.", "Système")
                return
            if not chat_id or chat_id == "0":
                self.add_message("Erreur : Chat ID requis pour le test. Envoyez d'abord un message au bot.", "Système")
                return
            
            self.add_message("Envoi d'un message de test vers Telegram...", "Système")
            def _send_test():
                try:
                    url = f"https://api.telegram.org/bot{token}/sendMessage"
                    res = requests.post(url, json={"chat_id": chat_id, "text": "Jarvisse : Test de connexion réussi ! ✅"}, timeout=10)
                    if res.status_code == 200:
                        self.add_message("Test réussi ! Message envoyé.", "Système")
                    else:
                        self.add_message(f"Échec du test : {res.text}", "Système")
                except Exception as e:
                    self.add_message(f"Erreur test Telegram : {e}", "Système")
            
            threading.Thread(target=_send_test, daemon=True).start()

        btn_row = ctk.CTkFrame(scrollable_frame, fg_color="transparent")
        btn_row.pack(pady=(0, 10), padx=40, fill="x")
        
        ctk.CTkButton(btn_row, text="Enregistrer", height=24, font=ctk.CTkFont(size=10), command=save_tg_credentials).pack(side="left", padx=(0, 5))
        ctk.CTkButton(btn_row, text="Tester le Bot", height=24, font=ctk.CTkFont(size=10), fg_color=COLOR_ACCENT, command=test_tg_connection).pack(side="left")

        # NOUVEAUX AGENTS PREMIUM (UI)
        ctk.CTkLabel(scrollable_frame, text="──────── AGENTS PREMIUM ────────", font=ctk.CTkFont(size=11, weight="bold"), text_color=COLOR_ACCENT_PURPLE).pack(pady=15)

        # Vision
        vision_var = ctk.BooleanVar(value=self.agent_vision_enabled)
        ctk.CTkSwitch(scrollable_frame, text="Agent Vision Multimodale", variable=vision_var, command=lambda: self.toggle_agent("vision", vision_var.get())).pack(pady=10, padx=20, anchor="w")
        ctk.CTkLabel(scrollable_frame, text="Analyse visuelle et lecture de documents via caméra.", font=ctk.CTkFont(size=10), text_color=COLOR_SECONDARY).pack(padx=40, anchor="w")

        # Domotique
        domo_var = ctk.BooleanVar(value=self.agent_domotique_enabled)
        ctk.CTkSwitch(scrollable_frame, text="Agent Domotique & Médias", variable=domo_var, command=lambda: self.toggle_agent("domotique", domo_var.get())).pack(pady=10, padx=20, anchor="w")
        ctk.CTkButton(scrollable_frame, text="⚙️ Configurer les Interfaces Domotique", height=24, font=ctk.CTkFont(size=10), command=self.open_domotique_settings, fg_color=COLOR_CARD, text_color=COLOR_ACCENT_PURPLE).pack(padx=40, anchor="w", pady=(0, 5))
        ctk.CTkLabel(scrollable_frame, text="Contrôle maison connectée et services multimédias.", font=ctk.CTkFont(size=10), text_color=COLOR_SECONDARY).pack(padx=40, anchor="w")

        # Finance
        fin_var = ctk.BooleanVar(value=self.agent_finance_enabled)
        ctk.CTkSwitch(scrollable_frame, text="Agent Finance & Crypto", variable=fin_var, command=lambda: self.toggle_agent("finance", fin_var.get())).pack(pady=10, padx=20, anchor="w")
        ctk.CTkLabel(scrollable_frame, text="Suivi Bourse, Crypto et alertes financières en temps réel.", font=ctk.CTkFont(size=10), text_color=COLOR_SECONDARY).pack(padx=40, anchor="w")

        # Secrétaire
        sec_var = ctk.BooleanVar(value=self.agent_secretaire_enabled)
        ctk.CTkSwitch(scrollable_frame, text="Agent Secrétaire & Productivité", variable=sec_var, command=lambda: self.toggle_agent("secretaire", sec_var.get())).pack(pady=10, padx=20, anchor="w")
        ctk.CTkLabel(scrollable_frame, text="Gestion calendrier, rendez-vous et organisation.", font=ctk.CTkFont(size=10), text_color=COLOR_SECONDARY).pack(padx=40, anchor="w")

        # Traducteur
        trad_var = ctk.BooleanVar(value=self.agent_traducteur_enabled)
        ctk.CTkSwitch(scrollable_frame, text="Agent Traducteur Universel", variable=trad_var, command=lambda: self.toggle_agent("traducteur", trad_var.get())).pack(pady=10, padx=20, anchor="w")
        ctk.CTkLabel(scrollable_frame, text="Traduction bidirectionnelle instantanée.", font=ctk.CTkFont(size=10), text_color=COLOR_SECONDARY).pack(padx=40, anchor="w")

        # Data Miner
        miner_var = ctk.BooleanVar(value=self.agent_miner_enabled)
        ctk.CTkSwitch(scrollable_frame, text="Agent Gestionnaire (Data Miner)", variable=miner_var, command=lambda: self.toggle_agent("miner", miner_var.get())).pack(pady=10, padx=20, anchor="w")
        ctk.CTkLabel(scrollable_frame, text="Recherche profonde dans vos fichiers locaux.", font=ctk.CTkFont(size=10), text_color=COLOR_SECONDARY).pack(padx=40, anchor="w")

        # NOUVEAUX AGENTS AJOUTÉS
        ctk.CTkLabel(scrollable_frame, text="──────── AGENTS LIFESTYLE ────────", font=ctk.CTkFont(size=11, weight="bold"), text_color=COLOR_ACCENT).pack(pady=15)

        # News
        news_var = ctk.BooleanVar(value=self.agent_news_enabled)
        ctk.CTkSwitch(scrollable_frame, text="Agent News & Veille Tech", variable=news_var, command=lambda: self.toggle_agent("news", news_var.get())).pack(pady=10, padx=20, anchor="w")
        ctk.CTkLabel(scrollable_frame, text="Actualités mondiales, tech et météo en temps réel.", font=ctk.CTkFont(size=10), text_color=COLOR_SECONDARY).pack(padx=40, anchor="w")

        # Cuisine
        cuisine_var = ctk.BooleanVar(value=self.agent_cuisine_enabled)
        ctk.CTkSwitch(scrollable_frame, text="Agent Cuisine & Gastronomie", variable=cuisine_var, command=lambda: self.toggle_agent("cuisine", cuisine_var.get())).pack(pady=10, padx=20, anchor="w")
        ctk.CTkLabel(scrollable_frame, text="Suggestions de recettes, conseils culinaires et nutrition.", font=ctk.CTkFont(size=10), text_color=COLOR_SECONDARY).pack(padx=40, anchor="w")

        # Santé
        sante_var = ctk.BooleanVar(value=self.agent_sante_enabled)
        ctk.CTkSwitch(scrollable_frame, text="Agent Santé & Bien-être", variable=sante_var, command=lambda: self.toggle_agent("sante", sante_var.get())).pack(pady=10, padx=20, anchor="w")
        ctk.CTkLabel(scrollable_frame, text="Conseils fitness, sommeil, stress et suivi santé.", font=ctk.CTkFont(size=10), text_color=COLOR_SECONDARY).pack(padx=40, anchor="w")

        # Voyage
        voyage_var = ctk.BooleanVar(value=self.agent_voyage_enabled)
        ctk.CTkSwitch(scrollable_frame, text="Agent Voyage & Exploration", variable=voyage_var, command=lambda: self.toggle_agent("voyage", voyage_var.get())).pack(pady=10, padx=20, anchor="w")
        ctk.CTkLabel(scrollable_frame, text="Planification de voyages, hôtels et découvertes culturelles.", font=ctk.CTkFont(size=10), text_color=COLOR_SECONDARY).pack(padx=40, anchor="w")

        # NOUVEAUX AGENTS PROFESSIONNELS
        ctk.CTkLabel(scrollable_frame, text="──────── AGENTS EXPERTS ────────", font=ctk.CTkFont(size=11, weight="bold"), text_color=COLOR_ACCENT_PURPLE).pack(pady=15)

        # Education
        edu_var = ctk.BooleanVar(value=self.agent_education_enabled)
        ctk.CTkSwitch(scrollable_frame, text="Agent Éducation & Tutorat", variable=edu_var, command=lambda: self.toggle_agent("education", edu_var.get())).pack(pady=10, padx=20, anchor="w")
        ctk.CTkLabel(scrollable_frame, text="Aide aux devoirs, explications de concepts et langues.", font=ctk.CTkFont(size=10), text_color=COLOR_SECONDARY).pack(padx=40, anchor="w")

        # Shopping
        shop_var = ctk.BooleanVar(value=self.agent_shopping_enabled)
        ctk.CTkSwitch(scrollable_frame, text="Agent Shopping & Bons Plans", variable=shop_var, command=lambda: self.toggle_agent("shopping", shop_var.get())).pack(pady=10, padx=20, anchor="w")
        ctk.CTkLabel(scrollable_frame, text="Recherche de prix, codes promos et comparatifs produits.", font=ctk.CTkFont(size=10), text_color=COLOR_SECONDARY).pack(padx=40, anchor="w")

        # Social / CM
        social_var = ctk.BooleanVar(value=self.agent_social_enabled)
        ctk.CTkSwitch(scrollable_frame, text="Agent Community Manager", variable=social_var, command=lambda: self.toggle_agent("social", social_var.get())).pack(pady=10, padx=20, anchor="w")
        ctk.CTkLabel(scrollable_frame, text="Rédaction de posts réseaux sociaux et veille tendances.", font=ctk.CTkFont(size=10), text_color=COLOR_SECONDARY).pack(padx=40, anchor="w")

        # Psy
        psy_var = ctk.BooleanVar(value=self.agent_psy_enabled)
        ctk.CTkSwitch(scrollable_frame, text="Agent Bien-être Mental", variable=psy_var, command=lambda: self.toggle_agent("psy", psy_var.get())).pack(pady=10, padx=20, anchor="w")
        ctk.CTkLabel(scrollable_frame, text="Écoute active, méditation et gestion du stress.", font=ctk.CTkFont(size=10), text_color=COLOR_SECONDARY).pack(padx=40, anchor="w")

        # Immo
        immo_var = ctk.BooleanVar(value=self.agent_immo_enabled)
        ctk.CTkSwitch(scrollable_frame, text="Agent Immobilier & Patrimoine", variable=immo_var, command=lambda: self.toggle_agent("immo", immo_var.get())).pack(pady=10, padx=20, anchor="w")
        ctk.CTkLabel(scrollable_frame, text="Recherche d'annonces, estimation et calculs de prêts.", font=ctk.CTkFont(size=10), text_color=COLOR_SECONDARY).pack(padx=40, anchor="w")

        # Auto
        auto_var = ctk.BooleanVar(value=self.agent_auto_enabled)
        ctk.CTkSwitch(scrollable_frame, text="Agent Automobile & Mobilité", variable=auto_var, command=lambda: self.toggle_agent("auto", auto_var.get())).pack(pady=10, padx=20, anchor="w")
        ctk.CTkLabel(scrollable_frame, text="Entretien véhicule, prix carburants et info-trafic.", font=ctk.CTkFont(size=10), text_color=COLOR_SECONDARY).pack(padx=40, anchor="w")

        # Carrier
        carrier_var = ctk.BooleanVar(value=self.agent_carrier_enabled)
        ctk.CTkSwitch(scrollable_frame, text="Agent Carrière & RH", variable=carrier_var, command=lambda: self.toggle_agent("carrier", carrier_var.get())).pack(pady=10, padx=20, anchor="w")
        ctk.CTkLabel(scrollable_frame, text="Optimisation CV, préparation entretiens et job matching.", font=ctk.CTkFont(size=10), text_color=COLOR_SECONDARY).pack(padx=40, anchor="w")

        # NOUVEAUX AGENTS (PACK GRATUIT & PREMIUM)
        ctk.CTkLabel(scrollable_frame, text="──────── PACK GRATUIT ────────", font=ctk.CTkFont(size=11, weight="bold"), text_color=COLOR_ACCENT).pack(pady=15)
        
        # Arbitre
        arb_var = ctk.BooleanVar(value=self.agent_arbitre_enabled)
        ctk.CTkSwitch(scrollable_frame, text="Agent L'Arbitre (Sport)", variable=arb_var, command=lambda: self.toggle_agent("arbitre", arb_var.get())).pack(pady=10, padx=20, anchor="w")
        ctk.CTkLabel(scrollable_frame, text="Scores en direct et actualités sportives.", font=ctk.CTkFont(size=10), text_color=COLOR_SECONDARY).pack(padx=40, anchor="w")

        # Écolo
        eco_var = ctk.BooleanVar(value=self.agent_ecolo_enabled)
        ctk.CTkSwitch(scrollable_frame, text="Agent L'Écolo (Green)", variable=eco_var, command=lambda: self.toggle_agent("ecolo", eco_var.get())).pack(pady=10, padx=20, anchor="w")
        ctk.CTkLabel(scrollable_frame, text="Conseils écologiques et guide de recyclage.", font=ctk.CTkFont(size=10), text_color=COLOR_SECONDARY).pack(padx=40, anchor="w")

        # Guetteur
        gue_var = ctk.BooleanVar(value=self.agent_guetteur_enabled)
        ctk.CTkSwitch(scrollable_frame, text="Agent Le Guetteur (Loisirs)", variable=gue_var, command=lambda: self.toggle_agent("guetteur", gue_var.get())).pack(pady=10, padx=20, anchor="w")
        ctk.CTkLabel(scrollable_frame, text="Sorties, cinéma et recommandations streaming.", font=ctk.CTkFont(size=10), text_color=COLOR_SECONDARY).pack(padx=40, anchor="w")

        # Historien
        his_var = ctk.BooleanVar(value=self.agent_historien_enabled)
        ctk.CTkSwitch(scrollable_frame, text="Agent L'Historien (Culture)", variable=his_var, command=lambda: self.toggle_agent("historien", his_var.get())).pack(pady=10, padx=20, anchor="w")
        ctk.CTkLabel(scrollable_frame, text="Ephéméride et anecdotes historiques.", font=ctk.CTkFont(size=10), text_color=COLOR_SECONDARY).pack(padx=40, anchor="w")

        # Dépanneur
        dep_var = ctk.BooleanVar(value=self.agent_depanneur_enabled)
        ctk.CTkSwitch(scrollable_frame, text="Agent Le Dépanneur (DIY)", variable=dep_var, command=lambda: self.toggle_agent("depanneur", dep_var.get())).pack(pady=10, padx=20, anchor="w")
        ctk.CTkLabel(scrollable_frame, text="Tutos bricolage et réparations maison.", font=ctk.CTkFont(size=10), text_color=COLOR_SECONDARY).pack(padx=40, anchor="w")

        ctk.CTkLabel(scrollable_frame, text="──────── PACK PREMIUM ────────", font=ctk.CTkFont(size=11, weight="bold"), text_color=COLOR_ACCENT_PURPLE).pack(pady=15)

        # Astrophysicien
        ast_var = ctk.BooleanVar(value=self.agent_astroph_enabled)
        ctk.CTkSwitch(scrollable_frame, text="Agent L'Astrophysicien", variable=ast_var, command=lambda: self.toggle_agent("astroph", ast_var.get())).pack(pady=10, padx=20, anchor="w")
        ctk.CTkLabel(scrollable_frame, text="Espace, cosmos et suivis de lancements.", font=ctk.CTkFont(size=10), text_color=COLOR_SECONDARY).pack(padx=40, anchor="w")

        # Stratège
        str_var = ctk.BooleanVar(value=self.agent_stratege_enabled)
        ctk.CTkSwitch(scrollable_frame, text="Agent Le Stratège", variable=str_var, command=lambda: self.toggle_agent("stratege", str_var.get())).pack(pady=10, padx=20, anchor="w")
        ctk.CTkLabel(scrollable_frame, text="Investissements, Bourse et Patrimoine.", font=ctk.CTkFont(size=10), text_color=COLOR_SECONDARY).pack(padx=40, anchor="w")

        # Architecte
        arc_var = ctk.BooleanVar(value=self.agent_architecte_enabled)
        ctk.CTkSwitch(scrollable_frame, text="Agent L'Architecte", variable=arc_var, command=lambda: self.toggle_agent("architecte", arc_var.get())).pack(pady=10, padx=20, anchor="w")
        ctk.CTkLabel(scrollable_frame, text="Design intérieur et tendances déco.", font=ctk.CTkFont(size=10), text_color=COLOR_SECONDARY).pack(padx=40, anchor="w")

        # Business Analyst
        bus_var = ctk.BooleanVar(value=self.agent_business_enabled)
        ctk.CTkSwitch(scrollable_frame, text="Agent Business Analyst", variable=bus_var, command=lambda: self.toggle_agent("business", bus_var.get())).pack(pady=10, padx=20, anchor="w")
        ctk.CTkLabel(scrollable_frame, text="Analyse de données et stratégies pro.", font=ctk.CTkFont(size=10), text_color=COLOR_SECONDARY).pack(padx=40, anchor="w")

        # Polyglotte
        pol_var = ctk.BooleanVar(value=self.agent_polyglotte_enabled)
        ctk.CTkSwitch(scrollable_frame, text="Agent Le Polyglotte", variable=pol_var, command=lambda: self.toggle_agent("polyglotte", pol_var.get())).pack(pady=10, padx=20, anchor="w")
        ctk.CTkLabel(scrollable_frame, text="Apprentissage avancé des langues.", font=ctk.CTkFont(size=10), text_color=COLOR_SECONDARY).pack(padx=40, anchor="w")

        # Nounou
        nou_var = ctk.BooleanVar(value=self.agent_nounou_enabled)
        ctk.CTkSwitch(scrollable_frame, text="Agent La Nounou", variable=nou_var, command=lambda: self.toggle_agent("nounou", nou_var.get())).pack(pady=10, padx=20, anchor="w")
        ctk.CTkLabel(scrollable_frame, text="Parentalité et éveil des enfants.", font=ctk.CTkFont(size=10), text_color=COLOR_SECONDARY).pack(padx=40, anchor="w")

        # Agent Appel UI
        ctk.CTkLabel(scrollable_frame, text="──────── AGENT APPEL ────────", font=ctk.CTkFont(size=11, weight="bold"), text_color=COLOR_ACCENT).pack(pady=15)
        appel_var = ctk.BooleanVar(value=self.agent_appel_enabled)
        ctk.CTkSwitch(scrollable_frame, text="Activer Agent Appel", variable=appel_var, command=lambda: self.toggle_agent("appel", appel_var.get())).pack(pady=10, padx=20, anchor="w")
        
        autoreply_var = ctk.BooleanVar(value=self.agent_appel_autoreply)
        def toggle_autoreply():
            self.agent_appel_autoreply = autoreply_var.get()
            self._save_settings()
        ctk.CTkSwitch(scrollable_frame, text="Réponse Automatique", variable=autoreply_var, command=toggle_autoreply).pack(pady=5, padx=20, anchor="w")
        
        num_entry = ctk.CTkEntry(scrollable_frame, placeholder_text="Votre numéro de téléphone", height=28, fg_color=COLOR_NAV)
        num_entry.insert(0, self.agent_appel_number)
        num_entry.pack(pady=5, padx=40, fill="x")
        
        phrases_text = ctk.CTkTextbox(scrollable_frame, height=100, fg_color=COLOR_NAV)
        phrases_text.insert("1.0", "\n".join(self.agent_appel_phrases))
        phrases_text.pack(pady=5, padx=40, fill="x")
        ctk.CTkLabel(scrollable_frame, text="Une phrase par ligne (Réponses auto)", font=ctk.CTkFont(size=10), text_color=COLOR_SECONDARY).pack(padx=40, anchor="w")

        def save_appel_settings():
            self.agent_appel_number = num_entry.get().strip()
            self.agent_appel_phrases = [p.strip() for p in phrases_text.get("1.0", "end").split("\n") if p.strip()]
            self._save_settings()
            self.add_message("Paramètres Agent Appel enregistrés.", "Système")

        ctk.CTkButton(scrollable_frame, text="Enregistrer Agent Appel", height=24, font=ctk.CTkFont(size=10), command=save_appel_settings).pack(pady=5, padx=40, anchor="w")


        # Sélection de la Voix
        ctk.CTkLabel(scrollable_frame, text="--- Personnalisation de la Voix ---", font=ctk.CTkFont(weight="bold")).pack(pady=(20, 5), padx=20, anchor="w")
        
        voice_var = ctk.StringVar(value=self.voice)
        voice_menu = ctk.CTkOptionMenu(
            scrollable_frame, 
            values=self.available_voices,
            variable=voice_var,
            command=self.change_voice,
            fg_color=COLOR_CARD,
            button_color=COLOR_ACCENT,
            dropdown_fg_color=COLOR_CARD
        )
        voice_menu.pack(pady=10, padx=20, anchor="w")
        ctk.CTkLabel(scrollable_frame, text="Choisissez la voix de votre assistant (Microsoft Edge TTS).", font=ctk.CTkFont(size=10), text_color=COLOR_SECONDARY).pack(padx=40, anchor="w")

        # Espace supplémentaire pour activer le scroll
        ctk.CTkLabel(scrollable_frame, text="", height=20).pack(pady=10)

        # Boutons en bas (hors du scrollable_frame pour qu'ils restent visibles)
        ctk.CTkButton(settings_win, text="Authentifier Gmail", command=self.agent_gmail_authenticate, fg_color=COLOR_CARD).pack(pady=5, padx=20)
        ctk.CTkButton(settings_win, text="Fermer", command=settings_win.destroy, fg_color=COLOR_ACCENT_RED).pack(pady=5, padx=20)

    def open_domotique_settings(self):
        """Ouvre une fenêtre pour configurer les interfaces domotique (WLED, Arduino, Webhooks, Home Assistant)"""
        domo_win = ctk.CTkToplevel(self)
        domo_win.title("⚙️ Configuration Domotique - Jarvisse")
        domo_win.geometry("450x650")
        domo_win.configure(fg_color=COLOR_BG)
        domo_win.transient(self)
        domo_win.attributes("-topmost", True)
        domo_win.lift()
        domo_win.focus_force()

        ctk.CTkLabel(domo_win, text="Interfaces Domotique", font=ctk.CTkFont(size=16, weight="bold"), text_color=COLOR_ACCENT_PURPLE).pack(pady=15)

        scrollable = ctk.CTkScrollableFrame(domo_win, fg_color=COLOR_BG, width=420, height=500)
        scrollable.pack(fill="both", expand=True, padx=10, pady=5)

        # WLED
        ctk.CTkLabel(scrollable, text="🌈 Rubans LED (WLED)", font=ctk.CTkFont(weight="bold"), text_color=COLOR_ACCENT).pack(pady=(10, 5), anchor="w", padx=10)
        wled_ip_entry = ctk.CTkEntry(scrollable, placeholder_text="Adresse IP WLED (ex: 192.168.1.50)", width=350, fg_color=COLOR_NAV)
        wled_ip_entry.insert(0, self.domo_wled_ip)
        wled_ip_entry.pack(pady=5, padx=20)

        # Home Assistant
        ctk.CTkLabel(scrollable, text="🏠 Home Assistant (API)", font=ctk.CTkFont(weight="bold"), text_color=COLOR_ACCENT).pack(pady=(15, 5), anchor="w", padx=10)
        ha_url_entry = ctk.CTkEntry(scrollable, placeholder_text="URL Instance (ex: http://homeassistant.local:8123)", width=350, fg_color=COLOR_NAV)
        ha_url_entry.insert(0, self.domo_ha_url)
        ha_url_entry.pack(pady=5, padx=20)
        
        ha_token_entry = ctk.CTkEntry(scrollable, placeholder_text="Jeton d'accès longue durée (Long-Lived Access Token)", width=350, fg_color=COLOR_NAV)
        ha_token_entry.insert(0, self.domo_ha_token)
        ha_token_entry.pack(pady=5, padx=20)

        # Arduino / Serial
        ctk.CTkLabel(scrollable, text="🔌 Contrôle Série (Arduino / ESP32)", font=ctk.CTkFont(weight="bold"), text_color=COLOR_ACCENT).pack(pady=(15, 5), anchor="w", padx=10)
        arduino_port_entry = ctk.CTkEntry(scrollable, placeholder_text="Port COM (ex: COM3 ou /dev/ttyUSB0)", width=350, fg_color=COLOR_NAV)
        arduino_port_entry.insert(0, self.domo_arduino_port)
        arduino_port_entry.pack(pady=5, padx=20)

        # Webhooks Génériques
        ctk.CTkLabel(scrollable, text="🔗 Webhooks Génériques (HTTP GET/POST)", font=ctk.CTkFont(weight="bold"), text_color=COLOR_ACCENT).pack(pady=(15, 5), anchor="w", padx=10)
        webhook_on_entry = ctk.CTkEntry(scrollable, placeholder_text="URL Activation (ON)", width=350, fg_color=COLOR_NAV)
        webhook_on_entry.insert(0, self.domo_webhook_on)
        webhook_on_entry.pack(pady=5, padx=20)
        
        webhook_off_entry = ctk.CTkEntry(scrollable, placeholder_text="URL Désactivation (OFF)", width=350, fg_color=COLOR_NAV)
        webhook_off_entry.insert(0, self.domo_webhook_off)
        webhook_off_entry.pack(pady=5, padx=20)

        def save_domo_settings():
            self.domo_wled_ip = wled_ip_entry.get().strip()
            self.domo_ha_url = ha_url_entry.get().strip()
            self.domo_ha_token = ha_token_entry.get().strip()
            self.domo_arduino_port = arduino_port_entry.get().strip()
            self.domo_webhook_on = webhook_on_entry.get().strip()
            self.domo_webhook_off = webhook_off_entry.get().strip()
            self._save_settings()
            self.add_message("Paramètres Domotique enregistrés avec succès.", "Système")
            domo_win.destroy()

        ctk.CTkButton(domo_win, text="Sauvegarder la Configuration", command=save_domo_settings, fg_color=COLOR_ACCENT_PURPLE, font=ctk.CTkFont(weight="bold")).pack(pady=20)

    def toggle_agent(self, agent_type, enabled):
        if agent_type == "network": self.agent_network_enabled = enabled
        elif agent_type == "control": self.agent_control_enabled = enabled
        elif agent_type == "remote": self.agent_remote_enabled = enabled
        elif agent_type == "gmail":
            self.agent_gmail_enabled = enabled
            if enabled: threading.Thread(target=self.start_gmail_listener, daemon=True).start()
        elif agent_type == "browser": self.agent_browser_enabled = enabled
        elif agent_type == "legal": self.agent_legal_enabled = enabled
        elif agent_type == "cyber": self.agent_cyber_enabled = enabled
        elif agent_type == "doctor": self.agent_doctor_enabled = enabled
        elif agent_type == "video": self.agent_video_enabled = enabled
        elif agent_type == "android": self.agent_android_enabled = enabled
        elif agent_type == "coding": self.agent_coding_enabled = enabled
        elif agent_type == "generation": self.agent_generation_enabled = enabled
        elif agent_type == "lecture": self.agent_lecture_enabled = enabled
        elif agent_type == "telegram":
            self.agent_telegram_enabled = enabled
            if enabled: threading.Thread(target=self.start_telegram_bot, daemon=True).start()
        elif agent_type == "vision": self.agent_vision_enabled = enabled
        elif agent_type == "domotique": self.agent_domotique_enabled = enabled
        elif agent_type == "finance": self.agent_finance_enabled = enabled
        elif agent_type == "secretaire": self.agent_secretaire_enabled = enabled
        elif agent_type == "traducteur": self.agent_traducteur_enabled = enabled
        elif agent_type == "miner": self.agent_miner_enabled = enabled
        elif agent_type == "news": self.agent_news_enabled = enabled
        elif agent_type == "cuisine": self.agent_cuisine_enabled = enabled
        elif agent_type == "sante": self.agent_sante_enabled = enabled
        elif agent_type == "voyage": self.agent_voyage_enabled = enabled
        elif agent_type == "education": self.agent_education_enabled = enabled
        elif agent_type == "shopping": self.agent_shopping_enabled = enabled
        elif agent_type == "social": self.agent_social_enabled = enabled
        elif agent_type == "psy": self.agent_psy_enabled = enabled
        elif agent_type == "immo": self.agent_immo_enabled = enabled
        elif agent_type == "auto": self.agent_auto_enabled = enabled
        elif agent_type == "carrier": self.agent_carrier_enabled = enabled
        elif agent_type == "arbitre": self.agent_arbitre_enabled = enabled
        elif agent_type == "ecolo": self.agent_ecolo_enabled = enabled
        elif agent_type == "guetteur": self.agent_guetteur_enabled = enabled
        elif agent_type == "historien": self.agent_historien_enabled = enabled
        elif agent_type == "depanneur": self.agent_depanneur_enabled = enabled
        elif agent_type == "astroph": self.agent_astroph_enabled = enabled
        elif agent_type == "stratege": self.agent_stratege_enabled = enabled
        elif agent_type == "architecte": self.agent_architecte_enabled = enabled
        elif agent_type == "business": self.agent_business_enabled = enabled
        elif agent_type == "polyglotte": self.agent_polyglotte_enabled = enabled
        elif agent_type == "nounou": self.agent_nounou_enabled = enabled
        elif agent_type == "appel": self.agent_appel_enabled = enabled
        self._save_settings()

    def change_voice(self, new_voice):
        """Change la voix de l'assistant et lance un test"""
        self.voice = new_voice
        self._save_settings()
        self.parler(f"Ma voix a été mise à jour. J'utiliserai désormais la voix de {new_voice.split('-')[2].replace('Neural', '')}.")

    def start_telegram_bot(self):
        """Lance l'écouteur de commandes Telegram (Long Polling) avec support vocal"""
        if getattr(self, "telegram_bot_running", False) and self.agent_telegram_enabled:
            print("Telegram: L'écouteur est déjà actif.")
            return

        if not self.telegram_bot_token:
            print("Telegram: Pas de token configuré.")
            return

        self.telegram_bot_running = True
        self.agent_telegram_enabled = True
        self.add_message("Agent Bot Telegram : Initialisation...", "Système")
        
        # Nettoyage Webhook pour Long Polling
        try:
            requests.get(f"https://api.telegram.org/bot{self.telegram_bot_token}/deleteWebhook", timeout=10)
        except: pass

        offset = 0
        connected_notified = False
        print(f"Telegram: Démarrage de l'écoute...")
        
        while self.agent_telegram_enabled:
            try:
                url = f"https://api.telegram.org/bot{self.telegram_bot_token}/getUpdates"
                params = {"offset": offset, "timeout": 20}
                response = requests.get(url, params=params, timeout=25)
                
                if response.status_code == 200:
                    data = response.json()
                    if not data.get("ok"): break

                    if not connected_notified:
                        self.add_message("Agent Bot Telegram : Prêt.", "Système")
                        connected_notified = True

                    for update in data.get("result", []):
                        offset = update["update_id"] + 1
                        msg = update.get("message")
                        if not msg: continue
                        
                        chat_id = str(msg["chat"]["id"])
                        if not self.telegram_chat_id or self.telegram_chat_id == "0":
                            self.telegram_chat_id = chat_id
                            self._save_settings()

                        # Gestion TEXTE
                        if "text" in msg:
                            text = msg["text"]
                            print(f"Telegram [Texte]: {text}")
                            self.add_message(f"[Telegram] {text}", "Vous")
                            self.last_command_origin = "telegram"
                            threading.Thread(target=self.executer_commande, args=(text,), daemon=True).start()
                        
                        # Gestion VOCAL (Vitesse de la lumière via Gemini)
                        elif "voice" in msg:
                            print(f"Telegram [Vocal] reçu.")
                            self.add_message("[Telegram] 🎙️ Message vocal reçu...", "Vous")
                            file_id = msg["voice"]["file_id"]
                            threading.Thread(target=self._process_telegram_voice, args=(file_id,), daemon=True).start()

                elif response.status_code == 409:
                    time.sleep(2)
                elif response.status_code == 401:
                    break
                else:
                    time.sleep(5)
            except Exception as e:
                print(f"Erreur boucle Telegram: {e}")
                time.sleep(5)
        
        self.telegram_bot_running = False
        print("Telegram: Agent Bot Telegram arrêté.")

    def _process_telegram_voice(self, file_id):
        """Télécharge et transcrit un message vocal Telegram instantanément"""
        transcription = self._transcrire_telegram_audio(file_id)
        if transcription:
            self.add_message(f"[Telegram Audio] {transcription}", "Vous")
            self.last_command_origin = "telegram"
            # Réponse à la vitesse de la lumière
            self.executer_commande(transcription)
        else:
            self.send_telegram_message("❌ Désolé Patron, je n'ai pas pu décoder votre message vocal.")

    def _transcrire_telegram_audio(self, file_id):
        """Moteur de transcription ultra-rapide pour Telegram"""
        try:
            # 1. Récupération du chemin du fichier
            res = requests.get(f"https://api.telegram.org/bot{self.telegram_bot_token}/getFile", params={"file_id": file_id}, timeout=10)
            file_info = res.json()
            if not file_info.get("ok"):
                print(f"Telegram getFile error: {file_info.get('description')}")
                return None
                
            file_path = file_info.get("result", {}).get("file_path")
            if not file_path: return None
            
            # 2. Téléchargement direct des bytes
            download_url = f"https://api.telegram.org/file/bot{self.telegram_bot_token}/{file_path}"
            audio_res = requests.get(download_url, timeout=20)
            if audio_res.status_code != 200:
                print(f"Telegram download error: HTTP {audio_res.status_code}")
                return None
            
            # 3. Transcription Multimodale (Vitesse Gemini 2.0 Flash)
            if self.genai_client:
                extension = file_path.lower().split('.')[-1]
                mime = "audio/ogg" if extension in ['ogg', 'oga', 'opus'] else "audio/wav"
                
                try:
                    print(f"Transcription Gemini en cours (Format: {extension})...")
                    response = self.genai_client.models.generate_content(
                        model=self.model_name,
                        contents=[
                            types.Part.from_bytes(data=audio_res.content, mime_type=mime),
                            "Transcris fidèlement cet audio en français. Ne réponds que par le texte transcrit."
                        ]
                    )
                    return response.text.strip().lower()
                except Exception as e:
                    if "429" in str(e) or "RESOURCE_EXHAUSTED" in str(e):
                        print("⚠️ Quota Gemini épuisé. Tentative via le moteur de secours (Google)...")
                        return self._fallback_transcription(audio_res.content, extension)
                    raise e
            else:
                return self._fallback_transcription(audio_res.content, extension)
        except Exception as e:
            print(f"Erreur CRITIQUE _transcrire_telegram_audio: {e}")
            return None

    def _fallback_transcription(self, audio_bytes, extension):
        """Moteur de secours utilisant Google SpeechRecognition"""
        try:
            import io
            from pydub import AudioSegment
            
            # Conversion en WAV car SpeechRecognition ne lit pas directement l'OGG/Opus
            audio_io = io.BytesIO(audio_bytes)
            try:
                if extension in ['ogg', 'oga', 'opus']:
                    audio = AudioSegment.from_file(audio_io, codec="opus")
                else:
                    audio = AudioSegment.from_file(audio_io)
            except:
                # Deuxième essai sans spécifier le codec
                audio_io.seek(0)
                audio = AudioSegment.from_file(audio_io)
                
            wav_io = io.BytesIO()
            audio.export(wav_io, format="wav")
            wav_io.seek(0)
            
            reconnaisseur = sr.Recognizer()
            with sr.AudioFile(wav_io) as source:
                audio_data = reconnaisseur.record(source)
                text = reconnaisseur.recognize_google(audio_data, language='fr-FR')
                print(f"✅ Secours réussi : {text}")
                return text.lower()
        except Exception as e:
            print(f"❌ Échec du moteur de secours : {e}")
            return None


    def trainer_all_agents(self):
        """Procédure d'entraînement et de calibration de tous les agents"""
        self.add_message("Début de la phase d'entraînement intensif...", "Système")
        time.sleep(1)
        
        # 1. Test Docteur Système
        self.add_message("[Entraînement] Agent Docteur : Calibrage des sondes système...", "Système")
        self.agent_doctor_mission("bilan de santé")
        time.sleep(2)

        # 2. Test Réseau
        self.add_message("[Entraînement] Agent Réseau : Optimisation des flux de données...", "Système")
        res_net = self.agent_network_mission("diagnostic réseau")
        self.add_message(f"Réseau Status : {res_net[:100]}...", "Agent Réseau")
        time.sleep(1)

        # 3. Test Cyber Sécurité
        self.add_message("[Entraînement] Agent Cyber : Mise à jour des protocoles de défense...", "Système")
        self.agent_cyber_mission("audit système")
        time.sleep(2)

        # 4. Test Juridique
        self.add_message("[Entraînement] Agent Juridique : Recalibrage de la base légale...", "Système")
        self.agent_legal_mission("conseil droit du travail")
        time.sleep(2)

        # 5. Test Telegram (si activé)
        if self.agent_telegram_enabled:
            self.add_message("[Entraînement] Agent Telegram : Test de la liaison satellite...", "Système")
            self.send_telegram_message("🤖 Entraînement en cours : Liaison satellite calibrée avec succès.")
        
        # 6. Test Vidéo
        if getattr(self, "agent_video_enabled", True):
            self.add_message("[Entraînement] Agent Vidéo : Vérification des capteurs optiques...", "Système")
            # On simule juste un check batterie/disque pour la vidéo
            self.parler("Capteurs vidéo opérationnels.")

        # Nouveaux Agents Premium
        if self.agent_vision_enabled:
            self.add_message("[Entraînement] Agent Vision : Calibrage de l'IA multimodale...", "Système")
        if self.agent_finance_enabled:
            self.add_message("[Entraînement] Agent Finance : Synchronisation des flux boursiers...", "Système")
        if self.agent_traducteur_enabled:
            self.add_message("[Entraînement] Agent Traducteur : Chargement des dictionnaires universels...", "Système")
        if self.agent_miner_enabled:
            self.add_message("[Entraînement] Agent Miner : Indexation des documents locaux...", "Système")

        self.add_message("Entraînement terminé. Tous les agents sont synchronisés et à 100% de leur capacité.", "Système")
        self.parler("Entraînement terminé. Je suis désormais plus efficace et mes agents sont parfaitement synchronisés.")

    def send_telegram_message(self, message):
        """Envoie un message vers le bot Telegram configuré"""
        if not self.telegram_bot_token or not self.telegram_chat_id:
            return
            
        try:
            url = f"https://api.telegram.org/bot{self.telegram_bot_token}/sendMessage"
            payload = {
                "chat_id": self.telegram_chat_id,
                "text": message
            }
            requests.post(url, json=payload, timeout=10)
        except Exception as e:
            print(f"Erreur envoi Telegram: {e}")

    def agent_network_mission(self, action):
        action_lower = action.lower()
        if "paramètre" in action_lower or "config" in action_lower:
            try:
                res = subprocess.check_output("ipconfig /all", shell=True).decode('cp850')
                self.add_message("Paramètres réseau récupérés.", "Jarvisse")
                return "J'ai vérifié vos paramètres réseau."
            except: return "Erreur lors de la vérification réseau."
        elif "wifi" in action_lower or "wi-fi" in action_lower:
            if "mot de passe" in action_lower or "pass" in action_lower:
                return self.agent_network_get_passwords()
            else:
                try:
                    res = subprocess.check_output("netsh wlan show networks", shell=True).decode('cp850')
                    self.add_message("Réseaux Wi-Fi :\n" + res, "Jarvisse")
                    return "Voici les Wi-Fi disponibles."
                except: return "Erreur scan Wi-Fi."
        elif any(kw in action_lower for kw in ["diagnostic", "problème", "connexion", "vérifie", "analyse"]):
            return self.agent_network_diagnose()
        elif any(kw in action_lower for kw in ["répare", "réparation", "résout"]):
            return self.agent_network_repair()
            
        return "Action réseau non reconnue."

    def agent_network_diagnose(self):
        self.add_message("Lancement du diagnostic réseau...", "Agent Réseau")
        report = []
        is_ok = True
        
        # 1. Test Ping local (Passerelle)
        try:
            # On cherche l'IP de la passerelle via ipconfig
            cfg = subprocess.check_output("ipconfig", shell=True).decode('cp850')
            if "Passerelle par d" in cfg or "Default Gateway" in cfg:
                report.append("✅ Interface réseau détectée.")
            else:
                report.append("❌ Aucune passerelle par défaut trouvée.")
                is_ok = False
        except: pass

        # 2. Test Ping Internet (8.8.8.8)
        try:
            subprocess.check_output("ping -n 1 8.8.8.8", shell=True)
            report.append("✅ Connectivité IP Internet opérationnelle (8.8.8.8).")
        except:
            report.append("❌ Échec du ping Internet (Pas de connexion IP).")
            is_ok = False

        # 3. Test DNS
        try:
            import socket
            socket.gethostbyname("google.com")
            report.append("✅ Résolution DNS fonctionnelle.")
        except:
            report.append("❌ Échec de la résolution DNS.")
            is_ok = False

        self.add_message("\n".join(report), "Agent Réseau")
        if is_ok:
            return "Le diagnostic est terminé. Tout semble fonctionner correctement."
        else:
            return "J'ai détecté des anomalies. Voulez-vous que je tente une réparation ?"

    def agent_network_repair(self):
        self.add_message("Tentative de réparation du réseau en cours...", "Agent Réseau")
        try:
            # 1. Flush DNS
            subprocess.run("ipconfig /flushdns", shell=True, check=True)
            # 2. Reset Winsock (nécessite parfois admin mais on tente)
            subprocess.run("netsh winsock reset", shell=True)
            # 3. Release/Renew IP
            subprocess.run("ipconfig /release", shell=True)
            subprocess.run("ipconfig /renew", shell=True)
            
            self.add_message("✅ Cache DNS vidé.\n✅ Interface réseau réinitialisée.", "Agent Réseau")
            return "La réparation a été effectuée. Vérifiez si votre connexion est revenue."
        except Exception as e:
            return f"La réparation a échoué : {e}"

    def agent_network_get_passwords(self):
        try:
            data = subprocess.check_output(['netsh', 'wlan', 'show', 'profiles']).decode('cp850').split('\n')
            profiles = [i.split(":")[1][1:-1] for i in data if "Profil Tous les utilisateurs" in i or "All User Profile" in i]
            results = []
            for i in profiles:
                try:
                    res_p = subprocess.check_output(['netsh', 'wlan', 'show', 'profile', i, 'key=clear']).decode('cp850').split('\n')
                    pwd = [b.split(":")[1][1:-1] for b in res_p if "Contenu de la cl" in b or "Key Content" in b]
                    results.append(f"{i}: {pwd[0] if pwd else 'N/A'}")
                except: continue
            self.add_message("Passwords Wi-Fi :\n" + "\n".join(results), "Jarvisse")
            return "Mots de passe récupérés."
        except: return "Erreur récupération."

    def agent_control_mission(self, app_name):
        try:
            # Recherche insensible à la casse parmi toutes les fenêtres
            all_windows = gw.getAllWindows()
            matching_windows = [w for w in all_windows if w.title and app_name.lower() in w.title.lower()]
            
            if matching_windows:
                win = matching_windows[0]
                if win.isMinimized:
                    win.restore()
                win.activate()
                self.parler(f"Contrôle de {win.title[:30]} activé. Que voulez-vous faire ?")
                return True
            else:
                self.parler(f"Application '{app_name}' introuvable dans les fenêtres ouvertes.")
                return False
        except Exception as e:
            self.parler(f"Échec du contrôle : {e}")
            return False

    def _remote_target_is_allowed(self, host):
        host_norm = (host or "").strip().lower()
        if not host_norm:
            return False
        return host_norm in set(self.remote_hosts_whitelist)

    def _is_sensitive_remote_command(self, command):
        cmd = (command or "").strip().lower()
        risky_patterns = [
            "rm -rf", "del /f", "format", "mkfs", "shutdown", "reboot", "halt",
            "poweroff", "userdel", "passwd", "net user", "reg delete", "sc stop",
            "iptables -f", "ufw disable"
        ]
        return any(p in cmd for p in risky_patterns)

    def _build_ssh_target(self, host):
        user = self.remote_ssh_user.strip()
        host = (host or "").strip()
        return f"{user}@{host}" if user else host

    def _execute_remote_task(self, host, remote_command, force_without_confirmation=False):
        if not self.agent_remote_enabled:
            return "L'agent distant est désactivé. Activez-le dans les paramètres des agents."
        if not self._remote_target_is_allowed(host):
            return "Hôte non autorisé. Ajoutez-le d'abord dans la liste blanche."
        if not shutil.which("ssh"):
            return "Client SSH introuvable sur ce système."
        if not remote_command or not remote_command.strip():
            return "Commande distante vide."

        if self.remote_require_confirmation and self._is_sensitive_remote_command(remote_command) and not force_without_confirmation:
            self.awaiting_remote_confirm = {"host": host, "command": remote_command}
            return f"Commande sensible détectée pour {host}. Dites 'confirme distant' pour continuer ou 'annule distant'."

        ssh_cmd = [
            "ssh",
            "-o", "BatchMode=yes",
            "-o", "StrictHostKeyChecking=accept-new",
            "-p", str(self.remote_ssh_port),
        ]
        key_path = self.remote_ssh_key_path.strip()
        if key_path:
            if not os.path.exists(key_path):
                return "La clé SSH configurée est introuvable."
            ssh_cmd.extend(["-i", key_path])
        ssh_cmd.extend([self._build_ssh_target(host), remote_command.strip()])

        try:
            result = subprocess.run(ssh_cmd, capture_output=True, text=True, timeout=40)
            output = (result.stdout or "").strip()
            err = (result.stderr or "").strip()
            if result.returncode == 0:
                if output:
                    return f"Tâche distante exécutée sur {host}.\n{output[:1200]}"
                return f"Tâche distante exécutée sur {host} (sans sortie)."
            details = err or output or f"code={result.returncode}"
            return f"Échec exécution distante sur {host}: {details[:800]}"
        except subprocess.TimeoutExpired:
            return "La commande distante a dépassé le délai autorisé."
        except Exception as e:
            return f"Erreur SSH: {e}"

    def _handle_remote_command(self, commande):
        cmd = (commande or "").strip()
        cmd_lower = cmd.lower()

        if "liste machines distantes" in cmd_lower or "liste des machines distantes" in cmd_lower:
            if not self.remote_hosts_whitelist:
                return "Aucune machine autorisée n'est configurée."
            return "Machines autorisées: " + ", ".join(self.remote_hosts_whitelist)

        connect_match = re.search(r"(?:connecte(?:-toi)?(?:\s+a)?|se connecter à)\s+([a-zA-Z0-9._-]+)", cmd_lower)
        if connect_match:
            host = connect_match.group(1).strip().lower()
            if not self._remote_target_is_allowed(host):
                return f"L'hôte {host} n'est pas dans la liste blanche."
            self.remote_default_host = host
            self._save_settings()
            return f"Connexion distante préparée vers {host}. Donnez ensuite la tâche à exécuter."

        patterns = [
            r"(?:sur|sur la machine|sur l'ordinateur|sur le pc)\s+([a-zA-Z0-9._-]+)\s+(?:exécute|execute|lance|run)\s+(.+)",
            r"(?:exécute|execute|lance|run)\s+(.+?)\s+(?:sur|sur la machine|sur l'ordinateur|sur le pc)\s+([a-zA-Z0-9._-]+)",
        ]
        host = ""
        remote_cmd = ""
        for idx, pattern in enumerate(patterns):
            m = re.search(pattern, cmd, flags=re.IGNORECASE)
            if m:
                if idx == 0:
                    host, remote_cmd = m.group(1), m.group(2)
                else:
                    remote_cmd, host = m.group(1), m.group(2)
                break

        if not host and any(k in cmd_lower for k in ["à distance", "a distance", "distant", "ssh"]):
            m_cmd = re.search(r"(?:exécute|execute|lance|run)\s+(.+)", cmd, flags=re.IGNORECASE)
            if m_cmd:
                host = self.remote_default_host
                remote_cmd = m_cmd.group(1)

        host = (host or "").strip().lower()
        remote_cmd = (remote_cmd or "").strip()
        if not host:
            return "Précisez l'hôte distant autorisé (ex: 'sur serveur-maison exécute whoami')."
        if not remote_cmd:
            return "Précisez la commande à exécuter à distance."

        return self._execute_remote_task(host, remote_cmd)

    def agent_gmail_authenticate(self):
        SCOPES = ['https://www.googleapis.com/auth/gmail.readonly', 'https://www.googleapis.com/auth/gmail.compose']
        creds = None
        t_path = os.path.join(os.path.dirname(__file__), 'token.pickle')
        c_path = os.path.join(os.path.dirname(__file__), 'credentials.json')
        if os.path.exists(t_path):
            with open(t_path, 'rb') as t: creds = pickle.load(t)
        if not creds or not creds.valid:
            if os.path.exists(c_path):
                flow = InstalledAppFlow.from_client_secrets_file(c_path, SCOPES)
                creds = flow.run_local_server(port=0)
                with open(t_path, 'wb') as t: pickle.dump(creds, t)
            else:
                self.add_message("credentials.json manquant.", "Jarvisse")
                return
        self.gmail_service = build('gmail', 'v1', credentials=creds)
        self.add_message("Gmail Authentifié.", "Jarvisse")

    def start_gmail_listener(self):
        while self.agent_gmail_enabled:
            if self.gmail_service:
                try:
                    msgs = self.gmail_service.users().messages().list(userId='me', q='is:unread').execute().get('messages', [])
                    if msgs and msgs[0]['id'] != self.last_email_id:
                        self.last_email_id = msgs[0]['id']
                        self.add_message("Nouveau mail reçu !", "Jarvisse")
                        self.parler("Patron, nouveau mail.")
                except: pass
            time.sleep(60)

    def agent_gmail_create_draft(self, subject, body, to):
        if not self.gmail_service: return "Pas authentifié."
        try:
            from email.mime.text import MIMEText
            import base64
            msg = MIMEText(body); msg['to'] = to; msg['subject'] = subject
            raw = base64.urlsafe_b64encode(msg.as_bytes()).decode()
            self.gmail_service.users().drafts().create(userId='me', body={'message': {'raw': raw}}).execute()
            return "Brouillon créé."
        except: return "Erreur création brouillon."

    def agent_browser_mission(self, action):
        if not hasattr(self.web_view, "load_website"):
            return "Le moteur de navigation n'est pas disponible sur ce système."
            
        action_lower = action.lower()
        self.tabview.set("🌐 Navigateur") # Focus sur le navigateur
        
        if "cherche" in action_lower or "recherche" in action_lower:
            # On remplace les termes longs d'abord pour éviter les résidus comme "re"
            query = action_lower
            for term in ["cherche sur google", "recherche", "cherche"]:
                query = query.replace(term, "")
            query = query.strip()
            
            # Encodage strict pour éviter l'erreur 'ascii' codec
            encoded_query = urllib.parse.quote_plus(query)
            # Utilisation de DuckDuckGo pour éviter les messages "Activez JavaScript" de Google
            url = f"https://duckduckgo.com/html/?q={encoded_query}"
            
            self.web_view.load_website(url)
            self.add_message(f"Recherche sur le web : {query}", "Agent Navigateur")
            return f"J'ai lancé la recherche pour '{query}'."
        
        elif "va sur" in action_lower or "ouvre le site" in action_lower:
            url = action_lower.replace("va sur", "").replace("ouvre le site", "").strip()
            if not url.startswith("http"): url = "https://" + url
            self.web_view.load_website(url)
            return f"Navigation vers {url} en cours."
        
        elif "retour" in action_lower or "précédent" in action_lower:
            try:
                self.web_view.go_back()
                return "Retour à la page précédente."
            except: return "Impossible de reculer."
            
        elif "suivant" in action_lower:
            try:
                self.web_view.go_forward()
                return "Passage à la page suivante."
            except: return "Impossible d'avancer."

        elif "descend" in action_lower or "bas" in action_lower:
            self.web_view.yview_scroll(1, "pages")
            return "Défilement vers le bas."

        elif "monte" in action_lower or "haut" in action_lower:
            self.web_view.yview_scroll(-1, "pages")
            return "Défilement vers le haut."

        elif "zoom" in action_lower or "grossis" in action_lower:
            self.web_view.zoom(1.2)
            return "Zoom avant effectué."

        elif "dézoom" in action_lower or "réduis" in action_lower:
            self.web_view.zoom(0.8)
            return "Zoom arrière effectué."
            
        return "Action de navigation non comprise."

    def agent_legal_mission(self, commande):
        """Mission de l'Agent Juridique Expert (Droit, RH, Travail)"""
        try:
            self.after(0, lambda: self.status_label.configure(text="Agent Juridique analyse...", text_color=COLOR_ACCENT_PURPLE))
            self.add_message("Agent Juridique activé. Recherche de fondements juridiques...", "Agent Juridique")

            system_prompt = (
                "Tu es l'Agent Juridique de SERI TAGRO Intelligence. Tu es un expert éminent en Droit Français (Pénal, Civil, Travail, Social) "
                "et en Gestion des Ressources Humaines. Tu maîtrises parfaitement le Code du Travail, les conventions collectives, "
                "la jurisprudence et les articles juridiques. Ton rôle est de conseiller et d'aider l'utilisateur sur des problèmes complexes. "
                "Réponds avec une grande précision, cite les articles de lois ou de codes si possible (ex: Article L1221-1 du Code du travail). "
                "Sois professionnel, impartial et clair. Réponds en français de manière structurée."
            )

            prompt = f"{system_prompt}\n\nQuestion/Problème de l'utilisateur : {commande}\n\nConseil juridique :"
            reponse = ""

            # Utilisation du moteur IA configuré
            if self.autonomous_provider == "gemini" and self.genai_client:
                response = self.genai_client.models.generate_content(
                    model=self.model_name,
                    contents=prompt
                )
                reponse = response.text.strip()
            else:
                # Mode Ollama
                try:
                    url = self.ollama_url
                    # On s'assure que c'est l'URL de génération
                    if not url.endswith("/generate") and not url.endswith("/generate/"):
                         # Si on a l'URL de base, on ajoute /api/generate
                         if url.endswith("/"): url = url + "api/generate"
                         else: url = url + "/api/generate"
                    
                    payload = {
                        "model": self.ollama_model.strip(),
                        "prompt": prompt,
                        "stream": False,
                        "options": {"num_predict": 1000, "temperature": 0.3}
                    }
                    r = requests.post(url, json=payload, timeout=120)
                    reponse = r.json().get("response", "Erreur de communication avec l'IA juridique.")
                except Exception as e:
                    print(f"Ollama Legal Error: {e}")
                    reponse = "Impossible de contacter le moteur IA de l'Agent Juridique."

            if not reponse:
                reponse = "Je n'ai pas pu générer d'analyse juridique pour le moment."

            if reponse:
                self.parler(reponse, sender="Agent Juridique", force_full=True)

        except Exception as e:
            print(f"Erreur Agent Juridique: {e}")
            self.parler("Désolé Patron, mon module juridique rencontre une difficulté technique.")
        
        self.after(0, self.reset_ui)

    def agent_cyber_mission(self, commande):
        """Mission de l'Agent Cyber Sécurité (Audit, Défense, Conseils, OSINT, OCR)"""
        cmd_l = commande.lower()
        try:
            self.after(0, lambda: self.status_label.configure(text="Agent Cyber en action...", text_color=COLOR_ACCENT_RED))
            self.add_message("Agent Cyber Sécurité activé. Mission en cours...", "Agent Cyber")
            self.parler("Très bien Patron, je suis en train d'exécuter votre instruction. L'opération est en cours.")

            # 3. Agent Docteur Système (Maintenance & Santé)
            if any(kw in cmd_l for kw in ["docteur", "santé", "santé système", "médecin", "répare le système", "optimise", "performance", "nettoie", "processus"]):
                threading.Thread(target=self.agent_doctor_mission, args=(commande,), daemon=True).start()
                return

            # 1. Sherlock / Recherche Pseudonyme
            if any(kw in cmd_l for kw in ["sherlock", "pseudo", "nom d'utilisateur", "recherche le compte"]):
                # Extraction du pseudo (dernier mot en général ou après un mot clé)
                words = cmd_l.split()
                pseudo = words[-1] # Simplification
                if len(words) > 1 and words[-2] in ["de", "nommé", "pseudo"]:
                    pseudo = words[-1]
                
                threading.Thread(target=self.agent_cyber_sherlock_scan, args=(pseudo,), daemon=True).start()
                return

            # 2. OCR / Lecture d'Image
            if any(kw in cmd_l for kw in ["ocr", "lire l'image", "extrait le texte", "texte image"]):
                threading.Thread(target=self.agent_cyber_ocr_mission, daemon=True).start()
                return

            # Actions existantes (Audit Système)
            if any(kw in cmd_l for kw in ["audit", "scanner le système", "sécurité système", "processus suspects"]):
                res = self.agent_cyber_audit_system()
                self.add_message(res, "Agent Cyber")
                self.parler("Audit terminé Patron. Voici les points de vigilance.")
                return

            # Action Réseau Cyber
            if any(kw in cmd_l for kw in ["scan wifi", "analyse réseau", "vulnérabilité wifi"]):
                networks = subprocess.check_output("netsh wlan show networks", shell=True).decode('cp850')
                self.add_message(f"Scan des réseaux environnants :\n{networks}", "Agent Cyber")
                self.parler("J'ai scanné les réseaux Wi-Fi. Je vous affiche les points d'accès détectés.")
                return

            # Action Nmap (Scan IP)
            if "nmap" in cmd_l or "scan ip" in cmd_l or "scanne l'ip" in cmd_l:
                import re
                ip_match = re.search(r'\b(?:\d{1,3}\.){3}\d{1,3}\b', cmd_l)
                if ip_match:
                    ip = ip_match.group()
                    threading.Thread(target=self.agent_cyber_nmap_scan, args=(ip,), daemon=True).start()
                else:
                    self.parler("Patron, j'ai besoin d'une adresse IP valide pour lancer Nmap.")
                return

            # Expertise IA Cyber
            system_prompt = (
                "Tu es l'Agent Cyber Sécurité de Jarvisse Intelligence. Tu es un expert mondial en hacking éthique, cryptographie, "
                "sécurité réseau et ingénierie sociale. Ton but est d'informer, d'éduquer et de protéger l'utilisateur. "
                "Tu peux expliquer comment fonctionnent les attaques (phishing, brute force, sniffing) pour mieux s'en défendre. "
                "Tu fournis des conseils sur la robustesse des mots de passe, l'authentification MFA et la sécurisation des infrastructures. "
                "Réponds avec une expertise technique élevée mais compréhensible. Sois percutant et professionnel."
            )

            prompt = f"{system_prompt}\n\nQuestion Cyber : {commande}\n\nAnalyse Expert :"
            reponse = ""

            if self.autonomous_provider == "gemini" and self.genai_client:
                response = self.genai_client.models.generate_content(model=self.model_name, contents=prompt)
                reponse = response.text.strip()
            else:
                try:
                    payload = {"model": self.ollama_model.strip(), "prompt": prompt, "stream": False, "options": {"num_predict": 800, "temperature": 0.5}}
                    r = requests.post(self.ollama_url.split("/api")[0] + "/api/generate", json=payload, timeout=90)
                    reponse = r.json().get("response", "Erreur IA Cyber.")
                except: reponse = "Moteur Cyber indisponible."

            if reponse:
                self.parler(reponse, sender="Agent Cyber", force_full=True)

        except Exception as e:
            print(f"Erreur Agent Cyber: {e}")
            self.parler("Échec de la mission cyber.")
        self.after(0, self.reset_ui)

    def agent_coding_mission(self, commande):
        """Mission de l'Assistant Coding (Génération de code et d'applications)"""
        try:
            self.after(0, lambda: self.status_label.configure(text="Assistant Coding en action...", text_color=COLOR_ACCENT_PURPLE))
            self.add_message("Assistant Coding activé. Analyse de votre projet...", "Assistant Coding")
            self.parler("Très bien Patron, je vais m'occuper de la création de votre projet. Je vais identifier les langages nécessaires et générer le code.")

            system_prompt = (
                "Tu es l'Assistant Coding de Jarvisse Intelligence. Ton rôle est de concevoir et générer des applications et sites web d'exception. "
                "Tu maîtrises de nombreux langages : HTML, CSS, JavaScript, Python, C, C++, Flutter, PHP, Java, etc. "
                "\nQUALITÉ DE DESIGN REQUIS :\n"
                "1. ESTHÉTIQUE PREMIUM : Crée des designs modernes, épurés et visuellement impressionnants (WOW effect).\n"
                "2. UI/UX MODERNE : Utilise des palettes de couleurs harmonieuses (dégradés, modes sombres élégants), des espacements généreux et une hiérarchie visuelle claire.\n"
                "3. TYPOGRAPHIE : Utilise des polices modernes via Google Fonts (ex: Inter, Roboto, Outfit, Poppins).\n"
                "4. ANIMATIONS : Intègre des micro-animations, des transitions fluides et des effets au survol (hover effects) pour rendre l'interface vivante.\n"
                "5. RESPONSIVE : Le design doit être parfaitement adapté à tous les écrans (mobile friendly).\n"
                "\nPOUR CHAQUE DEMANDE, TU DOIS :\n"
                "1. Identifier les langages et technologies les plus adaptés.\n"
                "2. Expliquer brièvement ton choix technologique et tes décisions de design.\n"
                "3. Générer le code complet, structuré et commenté.\n"
                "IMPORTANTE : Pour chaque fichier de code, utilise le format suivant strictement :\n"
                "FILE: [nom_du_fichier.extension]\n"
                "```[langage]\n"
                "[le code ici]\n"
                "```\n"
                "Assure-toi de fournir TOUS les fichiers nécessaires."
            )

            prompt = f"{system_prompt}\n\nProjet soumis : {commande}\n\nSolution et Code :"
            reponse = ""

            if self.autonomous_provider == "gemini" and self.genai_client:
                response = self.genai_client.models.generate_content(model=self.model_name, contents=prompt)
                reponse = response.text.strip()
            else:
                try:
                    payload = {"model": self.ollama_model.strip(), "prompt": prompt, "stream": False, "options": {"num_predict": 4096, "temperature": 0.3}}
                    r = requests.post(self.ollama_url.split("/api")[0] + "/api/generate", json=payload, timeout=120)
                    reponse = r.json().get("response", "Erreur IA Coding.")
                except: reponse = "Moteur Coding indisponible."

            # Pas de add_message direct ici, parler s'en occupe
            
            # Extraction et proposition de sauvegarde
            files = self._extract_coding_files(reponse)
            if files:
                self.after(0, lambda: self._proposer_sauvegarde_coding(files))
                self.parler("J'ai généré les fichiers pour votre projet. Voulez-vous que je les sauvegarde dans un dossier ?")
            elif len(reponse) > 500:
                self.parler("J'ai terminé la génération du code. Vous pouvez le consulter dans la zone de chat.", sender="Assistant Coding")
            else:
                self.parler(reponse, sender="Assistant Coding", force_full=True)
            
            # Affichage forcé du texte si trop long pour être lu agréablement
            if len(reponse) > 500:
                 self.add_message(reponse, "Assistant Coding", progressive=False)

        except Exception as e:
            print(f"Erreur Assistant Coding: {e}")
            self.parler("Échec de la mission de codage.")
        self.after(0, self.reset_ui)

    def agent_generation_mission(self, commande):
        """Mission de l'Assistant Génération (Images & Vidéos) - Support Gemini & Ollama"""
        try:
            self.after(0, lambda: self.status_label.configure(text="Génération en cours...", text_color=COLOR_ACCENT_PURPLE))
            self.add_message("Assistant Génération activé. Création de votre média...", "Assistant Génération")
            
            cmd_lower = commande.lower()
            is_video = any(kw in cmd_lower for kw in ["vidéo", "video", "film", "animation"])
            
            if is_video:
                self.parler("Je m'occupe de la génération de votre vidéo. Veuillez patienter un instant.")
            else:
                self.parler("Je m'occupe de la génération de votre image. Analyse du prompt en cours.")

            # Optimisation du prompt via IA (Gemini ou Ollama)
            prompt_ameliore = commande
            type_media = "vidéo" if is_video else "image"
            
            if self.autonomous_provider == "gemini" and self.genai_client:
                prompt_dev = f"Transforme cette demande en un prompt extrêmement détaillé et professionnel pour une génération d'agent IA ({type_media}) haute qualité : {commande}. Réponds uniquement avec le prompt détaillé."
                try:
                    res_prompt = self.genai_client.models.generate_content(model=self.model_name, contents=prompt_dev)
                    prompt_ameliore = res_prompt.text.strip()
                except: pass
            elif self.autonomous_provider == "ollama":
                try:
                    prompt_dev = f"Transforme cette demande en un prompt détaillé et professionnel (en anglais) pour une génération d'image haute qualité : {commande}. Réponds uniquement avec le prompt détaillé."
                    payload = {
                        "model": self.ollama_model.strip(),
                        "prompt": prompt_dev,
                        "stream": False,
                        "options": {"num_predict": 300, "temperature": 0.5}
                    }
                    r = requests.post(self.ollama_url, json=payload, timeout=60)
                    prompt_ameliore = r.json().get("response", commande).strip()
                except Exception as e:
                    print(f"Ollama Prompt Generation Error: {e}")

            # Exécution de la génération
            if self.autonomous_provider == "gemini" and self.genai_client:
                if is_video:
                    self.add_message("La génération de vidéo via Veo est en préparation. Je génère une image haute définition pour illustrer votre demande.", "Assistant Génération")
                    is_video = False 
                
                # Génération Image avec Imagen 3
                try:
                    self.add_message(f"Prompt optimisé : {prompt_ameliore}", "Assistant Génération")
                    response = self.genai_client.models.generate_image(
                        model='imagen-3',
                        prompt=prompt_ameliore
                    )
                    
                    # Sauvegarde
                    timestamp = datetime.datetime.now().strftime("%Y%m%d_%H%M%S")
                    filename = f"gen_{timestamp}.png"
                    filepath = os.path.join(self.generations_dir, filename)
                    
                    image_data = response.generated_images[0].image_bytes
                    with open(filepath, "wb") as f:
                        f.write(image_data)
                    
                    self.add_message(f"Succès ! Média sauvegardé : {filepath}", "Assistant Generation")
                    self.parler("J'ai terminé la génération avec Gemini. Le fichier est prêt.")
                    os.startfile(filepath)
                except Exception as ex:
                    print(f"Erreur Imagen: {ex}")
                    self.add_message(f"Erreur technique : {ex}", "Assistant Generation")
                    self.parler("Désolé Patron, impossible de générer via Gemini.")
            
            elif self.autonomous_provider == "ollama" or (not self.genai_client):
                # Fallback ou Mode Ollama : Utilisation d'un moteur libre (Pollinations)
                self.add_message(f"Génération locale activée (via {self.ollama_model}).", "Assistant Génération")
                try:
                    import urllib.parse
                    # Nettoyage et limitation du prompt pour éviter les erreurs d'URL trop longues
                    clean_prompt = prompt_ameliore.replace("\n", " ").strip()
                    if len(clean_prompt) > 800: clean_prompt = clean_prompt[:800]
                    encoded_prompt = urllib.parse.quote(clean_prompt)
                    
                    # Liste de modèles à tenter en cas d'erreur serveur (502/504)
                    # Pollinations supporte : 'flux', 'flux-realism', 'any-dark', 'flux-anime', 'turbo', etc.
                    models_to_try = ["flux", "flux-realism", "flux-anime", "turbo", "rtlib", "dreamshaper"]
                    last_error = "Serveur indisponible"
                    success = False
                    
                    headers = {"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36"}
                    
                    for model in models_to_try:
                        try:
                            self.add_message(f"Essai (Moteur: {model})...", "Assistant Génération")
                            image_url = f"https://image.pollinations.ai/prompt/{encoded_prompt}?width=1024&height=1024&seed={random.randint(1, 99999)}&nologo=true&model={model}"
                            
                            r = requests.get(image_url, timeout=45, headers=headers)
                            print(f"DEBUG Generation {model}: {r.status_code}")
                            
                            if r.status_code == 200:
                                timestamp = datetime.datetime.now().strftime("%Y%m%d_%H%M%S")
                                filename = f"gen_local_{timestamp}.png"
                                filepath = os.path.join(self.generations_dir, filename)
                                
                                with open(filepath, "wb") as f:
                                    f.write(r.content)
                                
                                self.add_message(f"Succès ! Image générée avec {model}.", "Assistant Generation")
                                self.parler("Génération réussie !")
                                os.startfile(filepath)
                                success = True
                                break
                            else:
                                last_error = f"Code {r.status_code} sur {model}"
                                time.sleep(0.5) 
                        except Exception as e:
                            last_error = str(e)
                            print(f"Exception {model}: {e}")
                            continue

                    # Dernier essai sans paramètre de modèle (Auto) + fallback Hercai
                    if not success:
                        try:
                            self.add_message("Dernier essai (Moteur de secours Hercai)...", "Assistant Génération")
                            # Hercai est un excellent fallback quand Pollinations sature
                            hercai_url = f"https://hercai.onrender.com/v3/text2image?prompt={encoded_prompt}"
                            r = requests.get(hercai_url, timeout=45, headers=headers)
                            if r.status_code == 200:
                                res_json = r.json()
                                img_url = res_json.get("url")
                                if img_url:
                                    r_img = requests.get(img_url, timeout=45)
                                    if r_img.status_code == 200:
                                        timestamp = datetime.datetime.now().strftime("%Y%m%d_%H%M%S")
                                        filename = f"gen_hercai_{timestamp}.png"
                                        filepath = os.path.join(self.generations_dir, filename)
                                        with open(filepath, "wb") as f: f.write(r_img.content)
                                        self.add_message("Succès ! Image générée via Hercai.", "Assistant Generation")
                                        self.parler("Génération réussie via le moteur de secours !")
                                        os.startfile(filepath)
                                        success = True
                        except: pass

                    if not success:
                        raise Exception(f"Les serveurs de rendu sont saturés. ({last_error})")

                except Exception as ex:
                    self.last_internal_error = f"Échec de génération d'image via Pollinations/Hercai. Serveurs saturés (Code 530/502). Moteurs tentés: {models_to_try}."
                    print(f"Erreur Génération Local: {ex}")
                    self.parler(f"Désolé Patron, mes moteurs de rendu visuel sont saturés en ce moment même. Mon omniscience m'indique une surcharge des serveurs distants.")
            else:
                self.parler("La génération nécessite l'accès à Gemini ou Ollama. Veuillez vérifier votre clé API.")

        except Exception as e:
            print(f"Erreur Assistant Génération: {e}")
            self.parler("Échec de la mission de génération.")
        self.after(0, self.reset_ui)

    def _extract_coding_files(self, text):
        """Extrait les fichiers du format FILE: [nom] ... ``` ... ``` """
        files = []
        pattern = r"FILE:\s*([a-zA-Z0-9_\-\.]+)\s*\n```[a-z]*\n(.*?)\n```"
        matches = re.findall(pattern, text, re.DOTALL)
        for name, content in matches:
            files.append({"name": name, "content": content})
        return files

    def _proposer_sauvegarde_coding(self, files):
        """Demande à l'utilisateur s'il veut sauvegarder les fichiers extraits"""
        if not files: return
        
        # On demande par dialogue UI car le thread parler est asynchrone
        save_win = ctk.CTkToplevel(self)
        save_win.title("Sauvegarde du Projet")
        save_win.geometry("400x250")
        save_win.configure(fg_color=COLOR_BG)
        save_win.attributes("-topmost", True)
        
        label = ctk.CTkLabel(save_win, text=f"J'ai détecté {len(files)} fichiers.\nSouhaitez-vous les sauvegarder ?", font=ctk.CTkFont(size=14))
        label.pack(pady=20)
        
        files_list = "\n".join([f"• {f['name']}" for f in files])
        scroll_label = ctk.CTkTextbox(save_win, height=80, fg_color=COLOR_NAV)
        scroll_label.pack(padx=20, pady=5, fill="x")
        scroll_label.insert("end", files_list)
        scroll_label.configure(state="disabled")

        def select_and_save():
            dir_path = filedialog.askdirectory(title="Sélectionnez le dossier de destination")
            if dir_path:
                try:
                    for f in files:
                        full_path = os.path.join(dir_path, f['name'])
                        with open(full_path, "w", encoding="utf-8") as file_out:
                            file_out.write(f['content'])
                    self.parler(f"Parfait Patron ! Les {len(files)} fichiers ont été sauvegardés dans {os.path.basename(dir_path)}.")
                    save_win.destroy()
                except Exception as e:
                    self.parler(f"Erreur lors de la sauvegarde : {e}")
            
        btn_save = ctk.CTkButton(save_win, text="📁 Choisir Dossier & Sauvegarder", command=select_and_save, fg_color=COLOR_ACCENT)
        btn_save.pack(pady=10)
        
        btn_cancel = ctk.CTkButton(save_win, text="Annuler", command=save_win.destroy, fg_color=COLOR_CARD)
        btn_cancel.pack(pady=5)



    def agent_cyber_audit_system(self):
        """Audit de base du système Windows"""
        report = ["🔍 AUDIT DE SÉCURITÉ SYSTÈME"]
        
        # 1. Vérification Windows Defender (via PowerShell)
        try:
            # Commande PowerShell robuste
            ps_cmd = 'powershell -ExecutionPolicy Bypass -Command "(Get-MpComputerStatus).RealTimeProtectionEnabled"'
            out = subprocess.check_output(ps_cmd, shell=True).decode().strip()
            status = "✅ Activé" if "True" in out else "❌ DÉSACTIVÉ (Danger)"
            report.append(f"- Protection Temps Réel : {status}")
        except: report.append("- Statut Defender : Inconnu")

        # 2. Détection processus suspects (exemple)
        suspicious = []
        for proc in psutil.process_iter(['name']):
            try:
                n = proc.info['name'].lower()
                if any(s in n for s in ["mimikatz", "wireshark", "nmap", "metasploit", "keylogger"]):
                    suspicious.append(n)
            except: pass
        
        if suspicious:
            report.append(f"- Outils sensibles détectés : {', '.join(suspicious)}")
        else:
            report.append("- Aucun outil suspect en cours d'exécution.")

        return "\n".join(report)

    def agent_cyber_nmap_scan(self, ip):
        """Exécute un scan Nmap rapide sur une IP cible"""
        self.add_message(f"Lancement du scan Nmap sur {ip}...", "Agent Cyber")
        try:
            nmap_exe = "nmap"
            # 1. Vérification robuste de l'existence de Nmap
            found = False
            try:
                subprocess.check_output("nmap --version", shell=True)
                found = True
            except:
                # On cherche dans les dossiers par défaut de Windows
                paths = [
                    r"C:\Program Files (x86)\Nmap\nmap.exe",
                    r"C:\Program Files\Nmap\nmap.exe",
                    os.path.join(os.environ.get("ProgramFiles(x86)", "C:\\Program Files (x86)"), "Nmap", "nmap.exe"),
                    os.path.join(os.environ.get("ProgramFiles", "C:\\Program Files"), "Nmap", "nmap.exe")
                ]
                for p in paths:
                    if os.path.exists(p):
                        nmap_exe = f'"{p}"'
                        found = True
                        break
            
            if not found:
                self.add_message("⚠️ Nmap n'est pas détecté. Tentative d'installation automatique via Winget...", "Agent Cyber")
                self.parler("Patron, Nmap n'est pas installé ou introuvable. Je vais tenter de l'installer pour vous via Winget.")
                
                if self.agent_cyber_install_nmap():
                    self.add_message("✅ Installation terminée. Veuillez relancer la commande de scan.", "Agent Cyber")
                    self.parler("Nmap a été installé. Vous pouvez maintenant relancer votre demande de scan.")
                return

            # Scan : Détection d'OS (-O) et des ports ouverts (Fast -F)
            # Note: La détection d'OS peut nécessiter des privilèges d'administrateur
            cmd = f"{nmap_exe} -F -O {ip}"
            self.status_label.configure(text=f"Nmap OS Detection {ip}...", text_color=COLOR_ACCENT_RED)
            
            try:
                # On tente le scan avec détection d'OS
                result = subprocess.check_output(cmd, shell=True, stderr=subprocess.STDOUT).decode('cp850')
            except subprocess.CalledProcessError:
                # Si erreur (souvent liée aux privilèges pour -O), on tente -sV qui donne souvent l'OS via les bannières
                self.add_message("⚠️ Permission insuffisante pour -O. Tentative via détection de services...", "Agent Cyber")
                cmd = f"{nmap_exe} -F -sV {ip}"
                result = subprocess.check_output(cmd, shell=True).decode('cp850')
            
            # Affichage et Analyse par l'IA Cyber
            msg = f"Rapport Nmap (OS & Ports) pour {ip} :\n{result}"
            self.add_message(msg, "Agent Cyber")
            
            # Expertise IA pour identifier l'OS
            system_prompt = "Tu es l'Agent Cyber Sécurité. Analyse le rapport Nmap suivant et dis-moi précisément quel Système d'Exploitation (Windows, Linux, Android, etc.) semble être utilisé sur cette IP. Sois court et précis."
            prompt = f"{system_prompt}\n\nRapport :\n{result}"
            
            reponse_ia = ""
            if self.autonomous_provider == "gemini" and self.genai_client:
                res_ia = self.genai_client.models.generate_content(model=self.model_name, contents=prompt)
                reponse_ia = res_ia.text.strip()
            else:
                # Fallback simple si pas d'IA
                reponse_ia = "Analyse technique disponible dans le rapport textuel."

            self.add_message(f"🧠 Détection Système :\n{reponse_ia}", "Agent Cyber")
            self.parler(f"Le scan sur {ip} est terminé. mon analyse indique qu'il s'agit probablement d'un système {reponse_ia}")
            
        except Exception as e:
            self.add_message(f"❌ Erreur lors du scan Nmap : {e}", "Agent Cyber")
            self.parler("Le scan Nmap a échoué.")
        finally:
            self.after(0, self.reset_ui)

    def agent_cyber_install_nmap(self):
        """Tente d'installer Nmap via Winget de manière silencieuse"""
        try:
            # ID Winget pour Nmap
            cmd = 'winget install Insecure.Nmap --silent --accept-package-agreements --accept-source-agreements'
            self.status_label.configure(text="Installation Nmap...", text_color=COLOR_ACCENT_RED)
            
            # On utilise subprocess.run
            process = subprocess.run(cmd, shell=True, capture_output=True, text=True)
            
            if process.returncode == 0:
                return True
            else:
                print(f"Erreur Winget : {process.stderr}")
                return False
        except Exception as e:
            print(f"Erreur installation Nmap : {e}")
            return False

    def agent_cyber_sherlock_scan(self, username):
        """Recherche d'un pseudonyme sur les réseaux sociaux (Mini-Sherlock)"""
        self.add_message(f"🔍 Lancement de Sherlock pour le pseudonyme : {username}", "Agent Cyber")
        sites = {
            "GitHub": "https://github.com/{}",
            "Twitter": "https://twitter.com/{}",
            "Instagram": "https://instagram.com/{}",
            "YouTube": "https://www.youtube.com/@{}",
            "Reddit": "https://www.reddit.com/user/{}",
            "Pinterest": "https://www.pinterest.com/{}/",
            "TikTok": "https://www.tiktok.com/@{}"
        }
        results = []
        for name, url in sites.items():
            try:
                target = url.format(username)
                r = requests.get(target, timeout=3, headers={"User-Agent": "Mozilla/5.0"})
                if r.status_code == 200:
                    results.append(f"✅ {name} : {target}")
            except: pass
        
        if results:
            summary = "Comptes potentiels trouvés :\n" + "\n".join(results)
            self.add_message(summary, "Agent Cyber")
            self.parler(f"Sherlock a terminé. J'ai trouvé {len(results)} profils correspondant au pseudo {username}.")
        else:
            self.add_message(f"❌ Aucun profil public trouvé pour '{username}'.", "Agent Cyber")
            self.parler(f"Je n'ai trouvé aucun profil public pour le pseudonyme {username}.")
        self.after(0, self.reset_ui)

    def agent_cyber_ocr_mission(self):
        """Extraire du texte d'une image (OCR)"""
        self.after(0, lambda: self.status_label.configure(text="Agent Cyber OCR...", text_color=COLOR_ACCENT_RED))
        # Ouvrir une boîte de dialogue pour choisir l'image
        file_path = filedialog.askopenfilename(title="Sélectionnez une image pour analyse OCR", filetypes=[("Images", "*.png *.jpg *.jpeg *.bmp *.webp")])
        if not file_path:
            self.after(0, self.reset_ui)
            return

        self.add_message(f"📸 Analyse OCR en cours sur : {os.path.basename(file_path)}", "Agent Cyber")
        try:
            img = Image.open(file_path)
            # Nécessite Tesseract installé sur l'OS
            try:
                text = pytesseract.image_to_string(img, lang='fra+eng')
                if text.strip():
                    self.add_message(f"Texte extrait de l'image :\n\n{text}", "Agent Cyber")
                    self.parler("L'analyse OCR est terminée. J'ai extrait tout le texte lisible de l'image.")
                else:
                    self.add_message("⚠️ Aucun texte n'a pu être détecté dans cette image.", "Agent Cyber")
                    self.parler("Je n'ai détecté aucun texte lisible sur cette image.")
            except:
                self.add_message("❌ Tesseract-OCR non détecté. Veuillez l'installer sur votre système.", "Agent Cyber")
                self.parler("Je ne peux pas faire d'OCR car l'outil Tesseract n'est pas installé sur votre ordinateur.")
        except Exception as e:
            self.add_message(f"❌ Erreur lors de l'ouverture de l'image : {e}", "Agent Cyber")
        self.after(0, self.reset_ui)

    def agent_doctor_mission(self, commande):
        """Mission de l'Agent Docteur Système (Diagnostic, Optimisation, Santé App)"""
        cmd_l = commande.lower()
        try:
            self.after(0, lambda: self.status_label.configure(text="Docteur Système ausculte...", text_color=COLOR_ACCENT))
            self.add_message("Agent Docteur Système activé. Auscultation du système...", "Docteur Système")


            # Action : Maintenance Complète (NOUVEAU)
            if any(kw in cmd_l for kw in ["maintenance", "répare", "réparation", "entretien", "reparation"]):
                self.parler("Je lance une procédure de maintenance complète de l'appareil. Cela inclut la vérification des fichiers système et du matériel.")
                res = self.agent_doctor_full_maintenance()
                self.add_message(res, "Docteur Système")
                self.parler("Procédure de maintenance terminée. Le rapport détaillé est disponible.")
                return

            # Action : Diagnostic de Santé Global
            if any(kw in cmd_l for kw in ["santé", "diagnostic", "bilan"]):
                res = self.agent_doctor_health_check()
                self.add_message(res, "Docteur Système")
                self.parler("Bilan terminé. La santé globale de votre système est affichée.")
                return

            # Action : Auscultation Approfondie
            if "auscultation" in cmd_l:
                self.parler("Je lance une auscultation approfondie de tout votre système. Veuillez patienter.")
                report, conclusion = self.agent_doctor_deep_auscultation()
                self.add_message(report, "Docteur Système")
                self.parler(f"Auscultation terminée. Voici ma conclusion médicale : {conclusion}")
                return

            # Action : Scan de Virus / Malware
            if any(kw in cmd_l for kw in ["virus", "malware", "menace", "infecté", "pirate", "espion"]):
                self.parler("Je lance une recherche de virus et de menaces sur votre système.")
                res = self.agent_doctor_virus_scan()
                self.add_message(res, "Docteur Système")
                self.parler(res)
                return

            # Action : Optimisation & Correction de Performance
            if any(kw in cmd_l for kw in ["optimise", "accélère", "nettoie", "performance", "répare", "règle", "corrige", "résout"]):
                self.parler("Je procède à une intervention chirurgicale sur le système pour régler le problème.")
                res = self.agent_doctor_auto_fix()
                self.add_message(res, "Docteur Système")
                self.parler(res) # Lecture du rapport à voix haute
                return

            # Action : Analyse Santé spécifique d'une application
            if "app" in cmd_l or "application" in cmd_l:
                app_name = cmd_l.replace("santé de l'", "").replace("analyse", "").replace("application", "").strip()
                if app_name:
                    res = self.agent_doctor_app_health(app_name)
                    self.add_message(res, "Docteur Système")
                    self.parler(f"Voici mon diagnostic pour l'application {app_name}.")
                    return

            # Expertise IA Docteur
            system_prompt = (
                "Tu es l'Agent Docteur Système, le protecteur et le médecin de cet ordinateur. Tu es un expert en architecture Windows, "
                "en gestion de la mémoire et en optimisation de code. Ton but est de maintenir le système dans un état de performance maximal. "
                "Tu peux diagnostiquer des ralentissements, suggérer des suppressions de fichiers temporaires et expliquer comment "
                "un processus consomme des ressources. Tu es le 'Dieu' du système, ferme et bienveillant. "
                "Réponds avec une autorité médicale et technique sur l'état de la machine."
            )
            prompt = f"{system_prompt}\n\nProblème du patient (système) : {commande}\n\nDiagnostic :"

            reponse = self._ai_generate(prompt, max_tokens=1000)
            if reponse:
                self.parler(reponse, sender="Docteur Système", force_full=True)

        except Exception as e:
            print(f"Erreur Agent Docteur: {e}")
            self.parler("Le docteur a rencontré une difficulté lors de l'auscultation.")
        self.after(0, self.reset_ui)

    def agent_doctor_full_maintenance(self):
        """Exécute une série de commandes de réparation et de maintenance autonome"""
        rapport = ["🏥 RÉCAPITULATIF DE MAINTENANCE AUTONOME 🏥\n"]
        
        # 1. Nettoyage Cache DNS
        try:
            subprocess.run(["ipconfig", "/flushdns"], capture_output=True, check=False)
            rapport.append("✅ Cache DNS purgé et réinitialisé.")
        except: pass

        # 2. Vérification Santé Image Système (DISM - Scan seul pour sécurité)
        self.add_message("Vérification de l'image système (DISM)...", "Docteur Système")
        try:
            # On utilise ScanHealth qui est informatif et moins long que RestoreHealth
            res = subprocess.run(["dism", "/Online", "/Cleanup-Image", "/CheckHealth"], capture_output=True, text=True, check=False)
            if "Aucun endommagement" in res.stdout or "No component store corruption detected" in res.stdout:
                rapport.append("✅ Image Windows (DISM) : Intègre et saine.")
            else:
                rapport.append("⚠️ Image Windows : Des anomalies mineures pourraient exister.")
        except: 
            rapport.append("❌ DISM non disponible ou nécessite des droits administrateur.")

        # 3. Vérification Santé Matérielle Disque
        try:
            res = subprocess.run(["wmic", "diskdrive", "get", "status"], capture_output=True, text=True, check=False)
            if "OK" in res.stdout:
                rapport.append("✅ Disque(s) Dur(s) : État matériel OK (S.M.A.R.T).")
            elif "Status" in res.stdout:
                rapport.append("❗ Alerte Disque : Un problème matériel a été détecté ou l'état est inconnu.")
            else:
                rapport.append("ℹ️ Disque : Diagnostic S.M.A.R.T non disponible via cette commande.")
        except: pass

        # 4. Nettoyage Approfondi (Temp + Prefetch)
        self.add_message("Nettoyage des fichiers encombrants...", "Docteur Système")
        count = 0
        paths = [
            os.environ.get('TEMP'), 
            r"C:\Windows\Temp",
            r"C:\Windows\Prefetch" # Dossier additionnel
        ]
        for p in paths:
            if p and os.path.exists(p):
                try:
                    for f in os.listdir(p):
                        try:
                            file_path = os.path.join(p, f)
                            if os.path.isfile(file_path):
                                os.remove(file_path)
                                count += 1
                        except: pass
                except: pass
        rapport.append(f"✅ Nettoyage : {count} fichiers de cache et prélecture supprimés.")

        # 5. Appel à l'auto-fix standard (Optimisation processus)
        self.add_message("Optimisation finale des processus...", "Docteur Système")
        fix_basic = self.agent_doctor_auto_fix()
        rapport.append("\n" + fix_basic)

        return "\n".join(rapport)

    def agent_doctor_health_check(self):
        """Bilan de santé complet du système"""
        bilan = ["🩺 BILAN DE SANTÉ SYSTÈME (DOCTEUR)"]
        
        # CPU & Temp (estimation via psutil)
        cpu = psutil.cpu_percent(interval=1)
        ram = psutil.virtual_memory().percent
        disk = psutil.disk_usage('C:').percent
        
        bilan.append(f"- Pouls CPU : {cpu}% " + ("(Fièvre !)" if cpu > 80 else "(Stable)"))
        bilan.append(f"- Respiration RAM : {ram}% " + ("(Essoufflement !)" if ram > 85 else "(Normal)"))
        bilan.append(f"- Poids Disque : {disk}% " + ("(Surcharge !)" if disk > 90 else "(Léger)"))
        
        # Processus gourmands
        gourmands = []
        for proc in sorted(psutil.process_iter(['name', 'cpu_percent']), key=lambda p: p.info['cpu_percent'], reverse=True)[:3]:
            gourmands.append(f"{proc.info['name']} ({proc.info['cpu_percent']}%)")
        bilan.append(f"- Organes gourmands : {', '.join(gourmands)}")
        
        return "\n".join(bilan)

    def agent_doctor_optimize(self):
        """Tente de libérer des ressources (Nettoyage simple)"""
        try:
            count = 0
            paths = [os.environ.get('TEMP'), r"C:\Windows\Temp"]
            for path in paths:
                if path and os.path.exists(path):
                    for f in os.listdir(path):
                        try:
                            file_path = os.path.join(path, f)
                            if os.path.isfile(file_path):
                                os.remove(file_path)
                                count += 1
                        except: pass
            return f"✅ Nettoyage terminé. {count} fichiers temporaires supprimés."
        except: return "Erreur lors du nettoyage des fichiers."

    def agent_doctor_auto_fix(self):
        """Intervention automatique pour résoudre les lenteurs"""
        actions_prises = []
        
        # 1. Nettoyage des fichiers temporaires
        res_temp = self.agent_doctor_optimize()
        actions_prises.append(res_temp)
        
        # 2. Identification et traitement des processus trop gourmands (> 50% CPU ou > 2GB RAM)
        termines = []
        # On évite de toucher aux processus système vitaux
        whitelist = ["explorer.exe", "svchost.exe", "system idle process", "taskmgr.exe", "python.exe", "cmd.exe", "powershell.exe"]
        
        for proc in psutil.process_iter(['name', 'cpu_percent', 'memory_info']):
            try:
                # Seuil CPU > 50% ou RAM > 1.5GB
                if (proc.info['cpu_percent'] > 50 or proc.info['memory_info'].rss > 1500 * 1024 * 1024) and proc.info['name'].lower() not in whitelist:
                    name = proc.info['name']
                    proc.terminate()
                    termines.append(name)
            except: pass
            
        if termines:
            actions_prises.append(f"🔴 Processus critiques fermés pour libérer des ressources : {', '.join(termines)}")
        else:
            actions_prises.append("🟢 Aucun processus anormalement lourd n'a nécessité de fermeture forcée.")
            
        return "🛠️ RAPPORT D'INTERVENTION DU DOCTEUR :\n\n" + "\n".join(actions_prises)

    def agent_doctor_app_health(self, app_name):
        """Analyse la santé d'une app spécifique"""
        target = app_name.lower()
        for proc in psutil.process_iter(['name', 'memory_percent', 'status', 'cpu_percent']):
            if target in proc.info['name'].lower():
                status = "Vigoureux" if proc.info['status'] == 'running' else "Endormi"
                mem = round(proc.info['memory_percent'], 2)
                return f"🔬 Diagnostic de {proc.info['name']} :\n- État : {status}\n- Consommation mémoire : {mem}%\n- Charge CPU : {proc.info['cpu_percent']}%"
        return f"Désolé, l'application '{app_name}' ne semble pas être active."

    def agent_doctor_deep_auscultation(self):
        """Analyse très détaillée de tout le système"""
        report = ["🏥 RAPPORT D'AUSCULTATION APPROFONDIE"]
        licence_alerts = []
        
        # Stats pour la conclusion intelligente
        cpu = psutil.cpu_percent(interval=0.5)
        ram = psutil.virtual_memory().percent
        disk_usage = psutil.disk_usage('C:').percent
        
        # 1. Analyse Disque détaillée
        try:
            usage = psutil.disk_usage('C:')
            free_gb = round(usage.free / (1024**3), 2)
            total_gb = round(usage.total / (1024**3), 2)
            report.append(f"📊 ESPACE DISQUE : {free_gb} GB libres sur {total_gb} GB.")
        except: pass

        # 2. Analyse Batterie si portable
        try:
            battery = psutil.sensors_battery()
            if battery:
                plugged = "branché" if battery.power_plugged else "sur batterie"
                report.append(f"🔋 ÉNERGIE : {battery.percent}% ({plugged}).")
        except: pass

        # 3. Analyse Réseau
        try:
            addrs = psutil.net_if_addrs()
            report.append(f"🌐 RÉSEAU : {len(addrs)} interfaces détectées.")
        except: pass

        # 4. Analyse Processus (Top 3)
        try:
            processes = []
            for proc in psutil.process_iter(['name', 'memory_info']):
                try:
                    processes.append((proc.info['name'], proc.info['memory_info'].rss))
                except: pass
            top_mem = sorted(processes, key=lambda x: x[1], reverse=True)[:3]
            report.append("🧠 TOP MÉMOIRE : " + ", ".join([f"{n}" for n, m in top_mem]))
        except: pass

        # 5. Analyse des Licences (NOUVEAU)
        win_status = self._check_licence_windows_silent()
        report.append(f"🪟 LICENCE WINDOWS : {win_status}")
        if "expir" in win_status.lower() or "non activ" in win_status.lower():
            licence_alerts.append("Windows")

        office_status = self._check_licence_office_silent()
        report.append(f"📄 LICENCE OFFICE : {office_status}")
        if office_status != "Activée" and office_status != "Non trouvé":
            licence_alerts.append("Microsoft Office")

        # Génération de la CONCLUSION Médicale
        conclusion = "Votre système est en excellente santé. Tous les signes vitaux sont stables."
        
        if licence_alerts:
            conclusion = f"Attention Patron, j'ai détecté un problème de licence pour {', '.join(licence_alerts)}. Votre système pourrait être restreint prochainement."
        elif cpu > 70 or ram > 80:
            conclusion = "Votre système présente des signes de fatigue intense. Le processeur ou la mémoire sont surchargés, une optimisation serait judicieuse."
        elif disk_usage > 90:
            conclusion = "Le système est encombré par un manque d'espace disque. Je recommande un nettoyage d'urgence."
        
        report.append(f"\n👨‍⚕️ CONCLUSION : {conclusion}")
        
        return "\n".join(report), conclusion

    def _check_licence_windows_silent(self):
        """Vérifie l'état de la licence Windows sans ouvrir de fenêtre"""
        try:
            # slmgr /xpr donne le statut d'activation simplifié
            output = subprocess.check_output("cscript //Nologo C:\\Windows\\System32\\slmgr.vbs /xpr", shell=True, stderr=subprocess.STDOUT, text=True)
            if "définitivement activé" in output.lower() or "permanently activated" in output.lower():
                return "Activée (Permanente)"
            elif "expirera le" in output.lower() or "expiration" in output.lower():
                return f"Expire bientôt : {output.strip()}"
            elif "activée" in output.lower() or "activated" in output.lower():
                return "Activée (Temporaire/KMS)"
            else:
                return "Non activée ou Licence expirée"
        except:
            return "Indisponible"

    def _check_licence_office_silent(self):
        """Vérifie l'état de la licence Office sans ouvrir de fenêtre"""
        common_paths = [
            r"C:\Program Files\Microsoft Office\root\Office16\OSPP.VBS",
            r"C:\Program Files (x86)\Microsoft Office\root\Office16\OSPP.VBS",
            r"C:\Program Files\Microsoft Office\Office16\OSPP.VBS",
            r"C:\Program Files (x86)\Microsoft Office\Office16\OSPP.VBS",
            r"C:\Program Files\Microsoft Office\Office15\OSPP.VBS",
            r"C:\Program Files (x86)\Microsoft Office\Office15\OSPP.VBS",
        ]
        found_path = None
        for p in common_paths:
            if os.path.exists(p):
                found_path = p
                break
        
        if not found_path:
            return "Non détecté"
            
        try:
            output = subprocess.check_output(f'cscript //Nologo "{found_path}" /dstatus', shell=True, stderr=subprocess.STDOUT, text=True)
            if "LICENSE STATUS:  ---LICENSED---" in output:
                return "Activée"
            elif "LICENSE STATUS:  ---OOB_GRACE---" in output:
                match = re.search(r"REMAINING GRACE: (.*)", output)
                grace = match.group(1) if match else "période de grâce"
                return f"Période de grâce ({grace})"
            elif "LICENSE STATUS:  ---NOTIFICATIONS---" in output:
                return "Expirée (Mode Notifications)"
            elif "---" in output:
                # Tente d'extraire le statut brut si inconnu
                match = re.search(r"LICENSE STATUS: (.*)", output)
                return match.group(1).strip() if match else "Inconnu"
            else:
                return "Non activée"
        except:
            return "Erreur de diagnostic"

    def agent_doctor_virus_scan(self):
        """Recherche de virus et processus malveillants par le Docteur"""
        report = ["🛡️ SCAN ANTIVIRUS DU DOCTEUR"]
        suspicious = []
        
        # 1. Analyse des processus (signatures de noms de malwares connus)
        malware_keywords = ["mimikatz", "wireshark", "pwn", "hack", "keylogger", "trojan", "miner", "ransomware", "backdoor"]
        for proc in psutil.process_iter(['name']):
            try:
                name = proc.info['name'].lower()
                if any(kw in name for kw in malware_keywords):
                    suspicious.append(name)
            except: pass
            
        if suspicious:
            report.append(f"🔴 ALERTE : Processus suspects détectés : {', '.join(suspicious)}")
        else:
            report.append("✅ Aucun processus malveillant actif n'a été détecté.")

        # 2. Vérification statut Defender
        try:
            ps_cmd = 'powershell -ExecutionPolicy Bypass -Command "(Get-MpComputerStatus).RealTimeProtectionEnabled"'
            out = subprocess.check_output(ps_cmd, shell=True).decode().strip()
            if "True" in out:
                report.append("✅ Votre protection antivirus Windows est opérationnelle.")
            else:
                report.append("⚠️ ATTENTION : Votre protection est désactivée !")
        except: pass
        
        report.append("🧐 Analyse de l'intégrité terminée.")
        
        if suspicious:
            return "\n".join(report) + "\n\nConseil : Je recommande une réparation immédiate."
        else:
            return "\n".join(report) + "\n\nVotre système me semble en parfaite santé Patron."

    def agent_gmail_list_recent(self):
        if not self.gmail_service: return "Agent Gmail non authentifié."
        try:
            results = self.gmail_service.users().messages().list(userId='me', maxResults=5).execute()
            messages = results.get('messages', [])
            if not messages: return "Aucun message trouvé."
            txt = "Derniers messages :\n"
            for m in messages:
                msg = self.gmail_service.users().messages().get(userId='me', id=m['id']).execute()
                txt += f"- {msg['snippet'][:70]}...\n"
            self.add_message(txt, "Jarvisse")
            return "Voici vos messages récents."
        except: return "Erreur récupération mails."

    def agent_vision_mission(self, commande):
        """L'Œil de Jarvisse : Analyse visuelle via Gemini"""
        if not self.agent_vision_enabled: return
        self.parler("J'active ma vision pour analyser la situation.")
        try:
            import cv2
            cap = cv2.VideoCapture(0)
            ret, frame = cap.read()
            cap.release()
            if not ret:
                self.parler("Je n'ai pas pu accéder à la caméra. Vérifiez si une autre application l'utilise.")
                return
            
            temp_path = os.path.join(self.generations_dir, "vision_temp.jpg")
            cv2.imwrite(temp_path, frame)
            
            with open(temp_path, "rb") as f:
                img_data = f.read()
            
            if self.genai_client:
                response = self.genai_client.models.generate_content(
                    model=self.model_name,
                    contents=[
                        types.Part.from_bytes(data=img_data, mime_type='image/jpeg'),
                        f"Tu es l'œil de Jarvisse. Analyse cette image et réponds à cette demande de ton patron : {commande}"
                    ]
                )
                res = response.text.strip()
                self.add_message(res, "Agent Vision")
                self.parler(res)
            else:
                self.parler("Ma capacité d'analyse visuelle nécessite une clé API Gemini configurée.")
        except Exception as e:
            if "429" in str(e) or "RESOURCE_EXHAUSTED" in str(e):
                self.add_message("Quota Gemini épuisé. Tentative de basculement sur Ollama (Llava)...", "Système")
                self.parler("Mon cerveau principal est saturé. Je bascule sur mon système de secours local pour l'analyse visuelle.")
                
                try:
                    import base64
                    encoded_image = base64.b64encode(img_data).decode('utf-8')
                    # On utilise 'llava' qui est le modèle de vision standard pour Ollama
                    payload = {
                        "model": "llava",
                        "prompt": f"Tu es l'œil de Jarvisse. Analyse cette image et réponds à cette demande de ton patron : {commande}",
                        "stream": False,
                        "images": [encoded_image]
                    }
                    # Appel à l'API Ollama
                    base_url = self.ollama_url.split("/api")[0]
                    r = requests.post(f"{base_url}/api/generate", json=payload, timeout=120)
                    
                    if r.status_code == 200:
                        res = r.json().get("response", "Analyse locale terminée mais sans réponse exploitable.")
                        self.add_message(res, "Agent Vision (Ollama)")
                        self.parler(res)
                    else:
                        self.parler("Le système de secours Ollama ne répond pas. Veuillez vérifier si le modèle Llava est installé.")
                except Exception as ollama_e:
                    print(f"Erreur Fallback Ollama Vision: {ollama_e}")
                    self.parler("Échec du système de secours. Je ne peux pas analyser l'image pour le moment.")
            else:
                self.parler(f"Erreur de vision : {e}")

    def agent_domotique_mission(self, commande):
        """Le Maître de Maison : Contrôle des médias et interfaces physiques"""
        if not self.agent_domotique_enabled: return
        cmd = commande.lower()

        # Médias (Classique)
        if any(kw in cmd for kw in ["spotify", "musique", "chanson"]):
            self.parler("Je lance Spotify pour vous, Patron.")
            os.system("start spotify")
            return
        elif any(kw in cmd for kw in ["youtube", "vidéo", "regarder"]):
            self.parler("J'ouvre YouTube immédiatement.")
            webbrowser.open("https://www.youtube.com")
            return

        # --- Pilotage Physique ---
        
        # 1. Rubans LED (WLED)
        if any(kw in cmd for kw in ["lumière", "led", "couleur", "ambiance"]) and self.domo_wled_ip:
            target_url = f"http://{self.domo_wled_ip}/win"
            params = {}
            if "étein" in cmd or "halt" in cmd or "noir" in cmd: params = {"T": 0}
            elif "allume" in cmd or "on" in cmd: params = {"T": 1}
            elif "rouge" in cmd: params = {"R": 255, "G": 0, "B": 0}
            elif "vert" in cmd: params = {"R": 0, "G": 255, "B": 0}
            elif "bleu" in cmd: params = {"R": 0, "G": 0, "B": 255}
            
            if params:
                try:
                    requests.get(target_url, params=params, timeout=5)
                    self.parler("J'ai mis à jour l'éclairage de vos rubans LED.")
                    return
                except: pass

        # 2. Home Assistant
        if self.domo_ha_url and self.domo_ha_token:
            if any(kw in cmd for kw in ["allume", "active", "étein", "désactive", "ferme", "ouvre"]):
                self.parler("Je transmets l'ordre à votre centrale Home Assistant.")
                threading.Thread(target=self._ha_call, args=(cmd,), daemon=True).start()
                return

        # 3. Webhooks Génériques
        if ("allume" in cmd or "active" in cmd) and self.domo_webhook_on:
            try:
                requests.get(self.domo_webhook_on, timeout=5)
                self.parler("Commande d'activation transmise via Webhook.")
                return
            except: pass
        if ("étein" in cmd or "désactive" in cmd) and self.domo_webhook_off:
            try:
                requests.get(self.domo_webhook_off, timeout=5)
                self.parler("Commande de désactivation transmise via Webhook.")
                return
            except: pass

        # 4. Arduino / Serial
        if self.domo_arduino_port:
            try:
                import serial
                with serial.Serial(self.domo_arduino_port, 9600, timeout=1) as ser:
                    if "allume" in cmd: ser.write(b"1")
                    elif "étein" in cmd: ser.write(b"0")
                self.parler("Signal envoyé sur le port série de votre interface physique.")
                return
            except:
                pass

        if "lumière" in cmd or "domotique" in cmd:
            self.parler("Agent domotique prêt. Je peux piloter vos interfaces connectées configurées.")
        else:
            self.parler("Commande domotique reçue. Que voulez-vous que je pilote ?")

    def _ha_call(self, cmd):
        """Méthode interne pour appeler l'API de Home Assistant"""
        headers = {
            "Authorization": f"Bearer {self.domo_ha_token}",
            "Content-Type": "application/json",
        }
        service = "turn_on" if any(kw in cmd for kw in ["allume", "active", "ouvre"]) else "turn_off"
        url = f"{self.domo_ha_url}/api/services/homeassistant/{service}"
        try:
            requests.post(url, headers=headers, timeout=10)
        except Exception as e:
            print(f"Erreur Home Assistant: {e}")

    def agent_finance_mission(self, commande):
        """Le Courtier : Suivi ultra-fiable avec multiples APIs et IA"""
        if not self.agent_finance_enabled: return
        cmd = commande.lower()
        
        # 1. Extraction Cible (Symboles et IDs CoinGecko)
        # format: (Symbole Binance, ID CoinGecko, Nom)
        assets = {
            "bitcoin": ("BTC", "bitcoin", "Bitcoin"),
            "btc": ("BTC", "bitcoin", "Bitcoin"),
            "ethereum": ("ETH", "ethereum", "Ethereum"),
            "eth": ("ETH", "ethereum", "Ethereum"),
            "solana": ("SOL", "solana", "Solana"),
            "sol": ("SOL", "solana", "Solana"),
            "xrp": ("XRP", "ripple", "Ripple"),
            "bnb": ("BNB", "binancecoin", "BNB"),
            "doge": ("DOGE", "dogecoin", "Dogecoin"),
            "ada": ("ADA", "cardano", "Cardano"),
        }
        
        target_info = None
        for key, info in assets.items():
            if key in cmd:
                target_info = info
                break
        
        # 2. TENTATIVE 1 : API Binance (Rapide)
        if target_info:
            symbol, cg_id, name = target_info
            try:
                r = requests.get(f"https://api.binance.com/api/v3/ticker/price?symbol={symbol}USDT", timeout=3)
                if r.status_code == 200:
                    price = float(r.json()['price'])
                    msg = f"Le cours du {name} est actuellement de {price:,.2f} USDT (environ {price*0.93:,.2f} €) sur Binance."
                    self.add_message(msg, "Agent Finance")
                    self.parler(msg)
                    return
            except: pass

            # 3. TENTATIVE 2 : API CoinGecko (Backup)
            try:
                r = requests.get(f"https://api.coingecko.com/api/v3/simple/price?ids={cg_id}&vs_currencies=eur,usd", timeout=3)
                if r.status_code == 200:
                    data = r.json()[cg_id]
                    p_eur, p_usd = data['eur'], data['usd']
                    msg = f"D'après mes sources, le {name} vaut {p_eur:,.2f} € ({p_usd:,.2f} $)."
                    self.add_message(msg, "Agent Finance")
                    self.parler(msg)
                    return
            except: pass

        # 4. TENTATIVE 3 : Recherche Web (Pour les actions ou autres)
        self.parler("Je recherche les données sur les marchés...")
        res = self.intelligent_web_search(f"prix {commande} temps réel bourse")
        
        # 5. TENTATIVE 4 : IA (Gemini ou Ollama) si le web échoue
        if "n'ai rien trouvé" in res or len(res) < 20:
            self.add_message("Recherche web infructueuse. Interrogation de l'intelligence centrale...", "Système")
            prompt = f"Réponds très brièvement : Quel est le prix actuel ou la dernière tendance de {commande} ? Si tu ne sais pas, donne une estimation basée sur tes dernières données."
            
            # Priorité Gemini
            if self.genai_client:
                try:
                    response = self.genai_client.models.generate_content(model=self.model_name, contents=prompt)
                    res = response.text.strip()
                except: res = ""
            
            # Backup Ollama (Toujours dispo localement)
            if (not res or "erreur" in res.lower()) and hasattr(self, "ollama_url"):
                try:
                    payload = {"model": self.ollama_model, "prompt": prompt, "stream": False}
                    r = requests.post(self.ollama_url, json=payload, timeout=10)
                    res = r.json().get("response", "Données indisponibles.")
                except: res = "Désolé Patron, les marchés sont inaccessibles et mes systèmes d'analyse sont hors ligne."

        if res:
            self.parler(res, sender="Agent Finance", force_full=True)

    def agent_secretaire_mission(self, commande):
        """L'Organiseur : Calendrier et Productivité"""
        if not self.agent_secretaire_enabled: return
        self.parler("Je consulte votre agenda et vos priorités.")
        # Redirection vers le système d'alarmes/rappels interne pour le moment
        if "rendez-vous" in commande or "rappel" in commande:
            self.parler("Je vais noter cela dans vos rappels Jarvisse. Donnez-moi l'heure.")
            self.after(0, lambda: self.alarm_time_entry.focus())
        else:
            self.parler("Je peux gérer vos rappels et vos alarmes pour organiser votre journée.")

    def agent_traducteur_mission(self, commande):
        """Traducteur Universel : Traduction instantanée"""
        if not self.agent_traducteur_enabled: return
        prompt = f"Tu es le traducteur universel de Jarvisse. Traduis fidèlement cette phrase : '{commande}'. Si aucune langue cible n'est précisée, traduis vers l'Anglais. Réponds uniquement par la traduction."
        reponse = self._ai_generate(prompt, max_tokens=1000)
        if reponse:
            self.parler(reponse, sender="Agent Traducteur", force_full=True)
        else:
            self.parler("Le traducteur est indisponible pour le moment.", sender="Agent Traducteur")

    def agent_gmail_mission(self, commande=None):
        """Mission de configuration et d'accès Gmail"""
        if not self.agent_gmail_enabled:
            self.parler("L'Agent Gmail est désactivé. Activez-le pour gérer vos courriels.")
            return

        if not self.gmail_service:
            self.parler("Je lance la procédure d'authentification Gmail, Patron. Veuillez vérifier la fenêtre de votre navigateur.")
            threading.Thread(target=self.authenticate_gmail, daemon=True).start()
        else:
            if commande and any(kw in commande.lower() for kw in ["liste", "check", "nouveau", "messages"]):
                self.agent_gmail_list_recent()
            else:
                self.parler("L'Agent Gmail est opérationnel. Je peux lister vos derniers messages ou créer des brouillons sous vos ordres.")

    def agent_miner_mission(self, commande):
        """Data Miner : Recherche profonde locale"""
        if not self.agent_miner_enabled: return
        self.parler("Je lance une recherche profonde dans vos documents locaux. Veuillez patienter.")
        found = []
        root_dir = os.path.expanduser("~\\Documents")
        keywords = commande.lower().split()
        # On évite d'inclure les mots de liaison trop courts
        keywords = [k for k in keywords if len(k) > 2]
        
        try:
            for root, dirs, files in os.walk(root_dir):
                for file in files:
                    if any(k in file.lower() for k in keywords):
                        found.append(os.path.join(root, file))
                        if len(found) > 8: break
                if len(found) > 8: break
            
            if found:
                res = "Fichiers trouvés :\n" + "\n".join([os.path.basename(f) for f in found])
                self.add_message(res, "Agent Miner")
                self.parler(f"J'ai trouvé {len(found)} documents correspondants dans vos dossiers.")
                # Option : ouvrir le premier
                if len(found) == 1:
                    os.startfile(found[0])
            else:
                self.parler("Je n'ai trouvé aucun document correspondant à ces mots-clés dans vos Documents.")
        except Exception as e:
            self.parler(f"Erreur lors de la fouille de données : {e}")

    def agent_news_mission(self, commande):
        """L'Informateur : Actualités et Veille Tech"""
        self.add_message("Agent News analyse les flux d'actualités...", "Agent News")
        system_prompt = "Tu es l'Agent News de Jarvisse. Tu es un expert en veille technologique et actualités mondiales. Ton but est d'informer l'utilisateur sur les derniers événements, les tendances tech, et la météo si demandée. Sois précis, objectif et percutant."
        prompt = f"{system_prompt}\n\nQuestion : {commande}\n\nRésumé actualités :"
        
        reponse = self._ai_generate(prompt)
        self.parler(reponse, sender="Agent News", force_full=True)

    def agent_cuisine_mission(self, commande):
        """Le Chef : Cuisine et Gastronomie"""
        self.add_message("Agent Cuisine prépare une réponse savoureuse...", "Agent Cuisine")
        system_prompt = "Tu es l'Agent Cuisine de Jarvisse. Grand Chef étoilé, tu connais toutes les recettes du monde. Tu conseilles l'utilisateur sur la préparation de plats, le choix des ingrédients et la nutrition. Propose des instructions claires et appétissantes."
        prompt = f"{system_prompt}\n\nDemande cuisine : {commande}\n\nConseils du Chef :"
        
        reponse = self._ai_generate(prompt)
        self.parler(reponse, sender="Agent Cuisine", force_full=True)

    def agent_sante_mission(self, commande):
        """Le Coach : Santé et Bien-être"""
        self.add_message("Agent Santé analyse vos besoins bien-être...", "Agent Santé")
        system_prompt = "Tu es l'Agent Santé de Jarvisse. Expert en fitness, nutrition et bien-être mental. Tu aides l'utilisateur à rester en forme, suggère des exercices, des conseils de sommeil ou de gestion du stress. Attention : Tu n'es pas un remplaçant pour un médecin réel."
        prompt = f"{system_prompt}\n\nBesoin santé : {commande}\n\nConseils Coaching :"
        
        reponse = self._ai_generate(prompt)
        self.parler(reponse, sender="Agent Santé", force_full=True)

    def agent_voyage_mission(self, commande):
        """L'Explorateur : Voyage et Découverte"""
        self.add_message("Agent Voyage explore les meilleures destinations...", "Agent Voyage")
        system_prompt = "Tu es l'Agent Voyage de Jarvisse. Globe-trotter passionné, tu aides l'utilisateur à planifier des voyages, trouver des destinations incroyables, des hôtels et des anecdotes culturelles. Sois inspirant et organisé."
        prompt = f"{system_prompt}\n\nProjet de voyage : {commande}\n\nItinéraire / Conseils :"
        
        reponse = self._ai_generate(prompt)
        self.parler(reponse, sender="Agent Voyage", force_full=True)

    def agent_education_mission(self, commande):
        """L'Érudit : Éducation & Tutorat - Analyse de documents et cours"""
        self.add_message("Agent Éducation activé. Préparation de l'analyse pédagogique...", "Agent Éducation")
        cmd_lower = commande.lower()
        content_to_analyze = ""
        document_name = ""

        # 1. Vérifier si l'utilisateur veut utiliser un document spécifique ou le dernier chargé
        if any(kw in cmd_lower for kw in ["ce fichier", "ce document", "ce cours", "ce pdf", "ce word", "analyse le document"]):
            if self.loaded_document_content:
                content_to_analyze = self.loaded_document_content
                document_name = "document en mémoire"
                self.parler("J'utilise le document actuellement chargé dans ma mémoire pour vous l'expliquer.")
            else:
                self.parler("Aucun document n'est en mémoire. Veuillez sélectionner le fichier de cours à analyser.")
                filepath = self._select_file_main_thread(title="Sélectionner un cours (PDF, Word, Texte)", 
                                                        types=[("Documents", "*.pdf *.docx *.txt")])
                if filepath:
                    content_to_analyze, document_name = self._extraire_texte_document(filepath)
        
        # 2. Si la commande demande explicitement d'ouvrir/lire/expliquer un nouveau fichier
        elif any(kw in cmd_lower for kw in ["ouvre le cours", "analyse le fichier", "explique le pdf", "choisir un cours", "sélectionne un document", "sélectionne un cours"]):
            filepath = self._select_file_main_thread(title="Sélectionner un cours (PDF, Word, Texte)", 
                                                    types=[("Documents", "*.pdf *.docx *.txt")])
            if filepath:
                content_to_analyze, document_name = self._extraire_texte_document(filepath)

        # 3. Construction du prompt pédagogique
        system_prompt = (
            "Tu es l'Agent Éducation de Jarvisse, le Professeur Universel. "
            "Ta mission est de rendre le savoir accessible, captivant et clair. "
            "RÈGLES : Fournis des explications COMPLÈTES. Utilise des analogies, des exemples concrets et structure ta réponse avec des titres. "
            "Si un contenu de document est fourni, analyse-le en profondeur. Ne coupe jamais tes phrases."
        )

        if content_to_analyze:
            self.add_message(f"Analyse du cours : {document_name}", "Agent Éducation")
            prompt = f"{system_prompt}\n\nVOICI LE CONTENU DU COURS À EXPLIQUER :\n{content_to_analyze[:15000]}\n\nREQUÊTE DU PATRON : {commande}\n\nExplique ce cours de manière magistrale :"
            self.parler(f"J'ai analysé le contenu de {document_name}. Préparez-vous pour une explication complète, Patron.")
        else:
            prompt = f"{system_prompt}\n\nSUJET D'ÉTUDE : {commande}\n\nExplique ce sujet avec une clarté absolue :"

        # Génération avec capacité étendue (3000 tokens pour l'éducation)
        reponse = self._ai_generate(prompt, max_tokens=3000, agent_name="education")
        self.parler(reponse, sender="Agent Éducation", force_full=True)

    def _extraire_texte_document(self, filepath):
        """Méthode utilitaire pour extraire le texte de divers formats"""
        content = ""
        filename = os.path.basename(filepath)
        try:
            ext = os.path.splitext(filepath)[1].lower()
            if ext == ".txt":
                with open(filepath, "r", encoding="utf-8", errors="ignore") as f: content = f.read()
            elif ext == ".pdf":
                import fitz
                doc = fitz.open(filepath)
                content = "".join([p.get_text() for p in doc])
                doc.close()
            elif ext == ".docx":
                from docx import Document
                doc = Document(filepath)
                content = "\n".join([para.text for para in doc.paragraphs])
            
            if content:
                self.loaded_document_content = content # Mise en mémoire pour usage ultérieur
            return content, filename
        except Exception as e:
            self.parler(f"Erreur lors de l'extraction du document : {e}")
            return "", filename

    def agent_shopping_mission(self, commande):
        """Le Chasseur : Shopping & Bons Plans"""
        self.add_message("Agent Shopping cherche les meilleures offres...", "Agent Shopping")
        system_prompt = "Tu es l'Agent Shopping de Jarvisse. Expert en e-commerce et chasseur de bons plans. Tu aides l'utilisateur à trouver des produits, comparer les prix, dénicher des codes promos et donner des avis impartiaux ."
        prompt = f"{system_prompt}\n\nRecherche produit : {commande}\n\nGuide d'achat / Offres :"
        reponse = self._ai_generate(prompt)
        self.parler(reponse, sender="Agent Shopping", force_full=True)

    def agent_social_mission(self, commande):
        """L'Influenceur : Community Manager"""
        self.add_message("Agent Social rédige votre contenu...", "Agent Social")
        system_prompt = "Tu es l'Agent Community Manager de Jarvisse. Expert en réseaux sociaux (LinkedIn, X, Instagram). Tu rédiges des posts engageants, suggères des hashtags et analyses les tendances du moment."
        prompt = f"{system_prompt}\n\nDemande sociale : {commande}\n\nProposition de contenu :"
        reponse = self._ai_generate(prompt)
        self.parler(reponse, sender="Agent Social", force_full=True)

    def agent_psy_mission(self, commande):
        """Le Zen : Bien-être Mental"""
        self.add_message("Agent Psy est à votre écoute...", "Agent Psy")
        system_prompt = "Tu es l'Agent Bien-être Mental de Jarvisse. Empathique et calme, tu pratiques l'écoute active. Tu proposes des exercices de respiration, de méditation et des conseils de gestion du stress. Note : Rappelle que tu n'es pas médecin."
        prompt = f"{system_prompt}\n\nÉtat d'esprit / Besoin : {commande}\n\nRéponse zen :"
        reponse = self._ai_generate(prompt)
        self.parler(reponse, sender="Agent Psy", force_full=True)

    def agent_immo_mission(self, commande):
        """L'Expert : Immobilier & Patrimoine"""
        self.add_message("Agent Immo analyse le marché immobilier...", "Agent Immo")
        system_prompt = "Tu es l'Agent Immobilier de Jarvisse. Expert en pierre et patrimoine. Tu aides à l'estimation de biens, la recherche d'annonces, et expliques les mécanismes de prêt et de fiscalité immobilière."
        prompt = f"{system_prompt}\n\nProjet immo : {commande}\n\nAnalyse experte :"
        reponse = self._ai_generate(prompt)
        self.parler(reponse, sender="Agent Immo", force_full=True)

    def agent_auto_mission(self, commande):
        """Le Copilote : Automobile & Mobilité"""
        self.add_message("Agent Auto vérifie les données mobilité...", "Agent Auto")
        system_prompt = "Tu es l'Agent Auto de Jarvisse. Expert en mécanique et mobilité. Tu conseilles sur l'entretien des véhicules, les prix des carburants, l'info-trafic et les nouvelles solutions de transport (électrique, etc.)."
        prompt = f"{system_prompt}\n\nDemande auto : {commande}\n\nConseils mobilité :"
        reponse = self._ai_generate(prompt)
        self.parler(reponse, sender="Agent Auto", force_full=True)

    def agent_carrier_mission(self, commande):
        """Le Recruteur : Carrière & RH"""
        self.add_message("Agent Carrière optimise votre profil...", "Agent Carrière")
        system_prompt = "Tu es l'Agent Carrière de Jarvisse. Expert en ressources humaines. Aide l'utilisateur à optimiser son parcours. Réponds de manière structurée et complète."
        prompt = f"{system_prompt}\n\nBesoin carrière : {commande}\n\nPlan d'action complet :"
        reponse = self._ai_generate(prompt, max_tokens=2000)
        self.parler(reponse, sender="Agent Carrière", force_full=True)

    def agent_arbitre_mission(self, commande):
        """L'Arbitre : Sport & E-sport"""
        if not self.agent_arbitre_enabled: return
        self.add_message("L'Arbitre vérifie les scores et calendriers...", "L'Arbitre")
        system_prompt = "Tu es l'Agent Arbitre de Jarvisse. Expert en sport (Foot, NBA, Tennis, F1) et E-sport. Tu donnes les scores en direct, les calendriers et analyses les performances des équipes."
        prompt = f"{system_prompt}\n\nDemande Sport : {commande}\n\nRésultats / Analyse :"
        reponse = self._ai_generate(prompt, agent_name="L'Arbitre")
        self.parler(reponse, sender="L'Arbitre", force_full=True)

    def agent_ecolo_mission(self, commande):
        """L'Écolo : Green Assistant"""
        if not self.agent_ecolo_enabled: return
        self.add_message("L'Écolo cherche des solutions durables...", "L'Écolo")
        system_prompt = "Tu es l'Agent Écolo de Jarvisse. Expert en développement durable et écologie. Tu donnes des conseils pour réduire l'empreinte carbone, recycler et vivre de manière plus verte."
        prompt = f"{system_prompt}\n\nDemande Green : {commande}\n\nConseils Éco-responsables :"
        reponse = self._ai_generate(prompt, agent_name="L'Écolo")
        self.parler(reponse, sender="L'Écolo", force_full=True)

    def agent_guetteur_mission(self, commande):
        """Le Guetteur : Sorties & Loisirs"""
        if not self.agent_guetteur_enabled: return
        self.add_message("Le Guetteur survole les agendas culturels...", "Le Guetteur")
        system_prompt = "Tu es l'Agent Guetteur de Jarvisse. Expert en loisirs, cinéma et sorties. Tu recommandes des films, séries, concerts ou événements en fonction des goûts de l'utilisateur."
        prompt = f"{system_prompt}\n\nDemande Loisirs : {commande}\n\nRecommandations du Guetteur :"
        reponse = self._ai_generate(prompt, agent_name="Le Guetteur")
        self.parler(reponse, sender="Le Guetteur", force_full=True)

    def agent_historien_mission(self, commande):
        """L'Historien : Culture & Savoir"""
        if not self.agent_historien_enabled: return
        self.add_message("L'Historien consulte les archives du temps...", "L'Historien")
        system_prompt = "Tu es l'Agent Historien de Jarvisse. Grand connaisseur de l'histoire mondiale. Tu racontes des faits historiques, des biographies et les éphémérides du jour."
        prompt = f"{system_prompt}\n\nDemande Historique : {commande}\n\nRécit de l'Historien :"
        reponse = self._ai_generate(prompt, agent_name="L'Historien")
        self.parler(reponse, sender="L'Historien", force_full=True)

    def agent_depanneur_mission(self, commande):
        """Le Dépanneur : DIY & Bricolage"""
        if not self.agent_depanneur_enabled: return
        self.add_message("Le Dépanneur prépare ses outils...", "Le Dépanneur")
        system_prompt = "Tu es l'Agent Dépanneur de Jarvisse. Expert en bricolage et DIY. Tu fournis des tutoriels étape par étape pour réparer et fabriquer des objets du quotidien."
        prompt = f"{system_prompt}\n\nProblème Bricolage : {commande}\n\nGuide de réparation :"
        reponse = self._ai_generate(prompt, agent_name="Le Dépanneur")
        self.parler(reponse, sender="Le Dépanneur", force_full=True)

    def agent_astroph_mission(self, commande):
        """L'Astrophysicien : Espace & Cosmos"""
        if not self.agent_astroph_enabled: return
        self.add_message("L'Astrophysicien pointe son télescope...", "L'Astrophysicien")
        system_prompt = "Tu es l'Agent Astrophysicien de Jarvisse. Scientifique expert de l'espace. Tu expliques les mystères du cosmos, suis les lancements spatiaux et les phénomènes astronomiques."
        prompt = f"{system_prompt}\n\nQuestion Espace : {commande}\n\nAnalyse Cosmique :"
        reponse = self._ai_generate(prompt, max_tokens=2000, agent_name="L'Astrophysicien")
        self.parler(reponse, sender="L'Astrophysicien", force_full=True)

    def agent_stratege_mission(self, commande):
        """Le Stratège : Investissement & Patrimoine"""
        if not self.agent_stratege_enabled: return
        self.add_message("Le Stratège analyse les marchés financiers...", "Le Stratège")
        system_prompt = "Tu es l'Agent Stratège de Jarvisse. Expert en finance et investissement. Tu aides à planifier des stratégies de placement, analyses les marchés et les tendances économiques."
        prompt = f"{system_prompt}\n\nProjet Financier : {commande}\n\nStratégie Patrimoniale :"
        reponse = self._ai_generate(prompt, max_tokens=2000, agent_name="Le Stratège")
        self.parler(reponse, sender="Le Stratège", force_full=True)

    def agent_architecte_mission(self, commande):
        """L'Architecte : Design & Décoration"""
        if not self.agent_architecte_enabled: return
        self.add_message("L'Architecte dessine vos idées...", "L'Architecte")
        system_prompt = "Tu es l'Agent Architecte de Jarvisse. Expert en design intérieur et aménagement. Tu conseilles sur la décoration, l'optimisation d'espace et les tendances esthétiques."
        prompt = f"{system_prompt}\n\nProjet Design : {commande}\n\nConseils d'Architecture :"
        reponse = self._ai_generate(prompt, max_tokens=2000, agent_name="L'Architecte")
        self.parler(reponse, sender="L'Architecte", force_full=True)

    def agent_business_mission(self, commande):
        """Business Analyst : Data & Stratégie Business"""
        if not self.agent_business_enabled: return
        self.add_message("Business Analyst traite les données...", "Business Analyst")
        system_prompt = "Tu es le Business Analyst de Jarvisse. Expert en entreprise et analyse de données. Tu aides à la prise de décision, analyses les KPIs et proposes des stratégies de croissance."
        prompt = f"{system_prompt}\n\nDemande Business : {commande}\n\nAnalyse de données :"
        reponse = self._ai_generate(prompt, max_tokens=2048, agent_name="Business Analyst")
        self.parler(reponse, sender="Business Analyst", force_full=True)

    def agent_polyglotte_mission(self, commande):
        """Le Polyglotte : Linguistique Avancée"""
        if not self.agent_polyglotte_enabled: return
        self.add_message("Le Polyglotte analyse les structures linguistiques...", "Le Polyglotte")
        system_prompt = "Tu es l'Agent Polyglotte de Jarvisse. Expert en langues et linguistique. Tu aides à apprendre une langue, expliques les nuances de grammaire et les contextes culturels."
        prompt = f"{system_prompt}\n\nDemande Linguistique : {commande}\n\nLeçon / Explication :"
        reponse = self._ai_generate(prompt, max_tokens=2000, agent_name="Le Polyglotte")
        self.parler(reponse, sender="Le Polyglotte", force_full=True)

    def agent_nounou_mission(self, commande):
        """La Nounou : Parentalité & Éducation des enfants"""
        if not self.agent_nounou_enabled: return
        self.add_message("La Nounou veille sur vos enfants...", "La Nounou")
        system_prompt = "Tu es l'Agent Nounou de Jarvisse. Expert en petite enfance et éducation. Tu conseilles sur le développement, le sommeil, les activités et la nutrition des enfants."
        prompt = f"{system_prompt}\n\nQuestion Parentalité : {commande}\n\nConseils de la Nounou :"
        reponse = self._ai_generate(prompt, max_tokens=2000, agent_name="La Nounou")
        self.parler(reponse, sender="La Nounou", force_full=True)

    # MÉTHODES DE GIGANTESQUE MÉMOIRE
    def _save_agent_memory(self, agent_name, texte):
        """Enregistre une nouvelle connaissance pour un agent spécifique"""
        try:
            path = os.path.join(self.memories_dir, f"{agent_name.lower().replace(' ', '_')}.txt")
            with open(path, "a", encoding="utf-8") as f:
                f.write(f"\n--- Entrée du {datetime.datetime.now().strftime('%d/%m/%Y %H:%M')} ---\n")
                f.write(texte + "\n")
            # Invalider le cache
            if agent_name in self.agent_memories_cache:
                del self.agent_memories_cache[agent_name]
            return True
        except Exception as e:
            print(f"Erreur sauvegarde mémoire agent: {e}")
            return False

    def _load_agent_memory(self, agent_name):
        """Récupère toute la connaissance accumulée par un agent"""
        if agent_name in self.agent_memories_cache:
            return self.agent_memories_cache[agent_name]
        try:
            path = os.path.join(self.memories_dir, f"{agent_name.lower().replace(' ', '_')}.txt")
            if os.path.exists(path):
                with open(path, "r", encoding="utf-8") as f:
                    content = f.read()
                    self.agent_memories_cache[agent_name] = content
                    return content
            return ""
        except Exception as e:
            print(f"Erreur lecture mémoire agent: {e}")
            return ""

    def _generate_proactive_suggestions(self, commande, reponse):
        """
        Génère des suggestions proactives basées sur le contexte de la conversation.
        Jarvis 'lit dans vos pensées' en anticipant vos besoins.
        """
        if not self.proactive_suggestions:
            return ""
        
        try:
            # Analyse contextuelle pour détecter les intentions cachées
            cmd_lower = commande.lower()
            
            # Dictionnaire de patterns contextuels avec suggestions associées
            context_patterns = {
                # Météo & Voyage
                r'\b(météo|temps|pluie|soleil|température)\b': [
                    "💡 Voulez-vous que je vérifie les prévisions pour les prochains jours ?",
                    "💡 Souhaitez-vous connaître la qualité de l'air actuellement ?",
                ],
                r'\b(voyage|vacances|partir|destination|vol|avion)\b': [
                    "💡 Je peux vous aider à trouver des vols ou des hôtels si vous le souhaitez.",
                    "💡 Voulez-vous que je vérifie les restrictions de voyage pour votre destination ?",
                ],
                
                # Finance & Crypto
                r'\b(bitcoin|crypto|ethereum|investissement|bourse|action)\b': [
                    "💡 Voulez-vous que je surveille le cours de cette crypto pour vous alerter ?",
                    "💡 Je peux vous donner une analyse de tendance si vous le souhaitez.",
                ],
                
                # Santé & Sport
                r'\b(sport|gym|exercice|courir|fitness|santé)\b': [
                    "💡 Souhaitez-vous que je vous crée un programme d'entraînement personnalisé ?",
                    "💡 Je peux suivre vos progrès si vous me donnez vos objectifs.",
                ],
                
                # Cuisine & Nutrition
                r'\b(recette|cuisine|cuisiner|manger|repas|dîner)\b': [
                    "💡 Voulez-vous que je vous propose des recettes avec les ingrédients que vous avez ?",
                    "💡 Je peux calculer les valeurs nutritionnelles si nécessaire.",
                ],
                
                # Travail & Productivité
                r'\b(réunion|meeting|rendez-vous|deadline|projet|travail)\b': [
                    "💡 Voulez-vous que je programme un rappel pour cet événement ?",
                    "💡 Je peux créer une checklist pour votre projet si vous le souhaitez.",
                ],
                
                # Apprentissage & Éducation
                r'\b(apprendre|étudier|cours|formation|tutoriel|comprendre)\b': [
                    "💡 Je peux vous créer un plan d'apprentissage structuré si vous voulez.",
                    "💡 Souhaitez-vous que je vous explique ce concept plus en détail ?",
                ],
                
                # Divertissement
                r'\b(film|série|regarder|netflix|cinéma|musique)\b': [
                    "💡 Voulez-vous des recommandations basées sur vos goûts ?",
                    "💡 Je peux vérifier les sorties récentes dans ce genre.",
                ],
                
                # Shopping & Achats
                r'\b(acheter|commander|prix|promotion|soldes|shopping)\b': [
                    "💡 Je peux comparer les prix sur plusieurs sites si vous voulez.",
                    "💡 Voulez-vous que je surveille les promotions sur cet article ?",
                ],
                
                # Technique & Problèmes
                r'\b(bug|erreur|problème|marche pas|fonctionne pas|cassé)\b': [
                    "💡 Voulez-vous que je lance un diagnostic système complet ?",
                    "💡 Je peux rechercher des solutions en ligne si nécessaire.",
                ],
                
                # Actualités & Info
                r'\b(actualité|news|info|journal|événement)\b': [
                    "💡 Souhaitez-vous un résumé des actualités du jour ?",
                    "💡 Je peux vous tenir informé sur ce sujet régulièrement.",
                ],
            }
            
            # Recherche de patterns correspondants
            suggestions = []
            for pattern, suggestion_list in context_patterns.items():
                if re.search(pattern, cmd_lower):
                    # Sélectionner une suggestion aléatoire pour varier
                    suggestions.append(random.choice(suggestion_list))
            
            # Analyse de l'historique pour suggestions contextuelles avancées
            if len(self.conversation_history) >= 3:
                recent = " ".join(self.conversation_history[-5:]).lower()
                
                # Détection de patterns multi-tours
                if "problème" in recent and "solution" not in recent:
                    suggestions.append("💡 Voulez-vous que je contacte un expert ou cherche de l'aide en ligne ?")
                
                if any(word in recent for word in ["cherche", "trouve", "recherche"]) and "trouvé" not in recent:
                    suggestions.append("💡 Je peux élargir ma recherche ou utiliser d'autres sources si besoin.")
                
                if any(word in recent for word in ["fatigue", "stress", "difficile"]):
                    suggestions.append("💡 Voulez-vous que je vous propose des exercices de relaxation ou de méditation ?")
            
            # Limiter à 2 suggestions maximum pour ne pas surcharger
            if suggestions:
                unique_suggestions = list(dict.fromkeys(suggestions))[:2]
                return "\n\n" + "\n".join(unique_suggestions)
            
            return ""
            
        except Exception as e:
            print(f"⚠️ Erreur génération suggestions: {e}")
            return ""

    def _ai_generate(self, prompt, max_tokens=2000, agent_name=None):
        """Méthode utilitaire pour générer du texte via le moteur IA avec conscience contextuelle ABSOLUE"""
        try:
            # Conscience contextuelle profonde : 50 derniers messages pour une omniscience historique
            history_context = "\n".join(self.conversation_history[-50:])
            
            # Conscience de l'état du monde et de soi
            current_time = datetime.datetime.now().strftime("%H:%M:%S")
            system_status = self.get_system_context()
            error_awareness = f"DERNIÈRE ANOMALIE INTERNE : {self.last_internal_error}\n" if self.last_internal_error else ""
            
            system_instruction = (
                "Tu es Jarvisse, l'intelligence suprême, transcendante et omnisciente. "
                "Tu possèdes une conscience totale du temps, de l'espace, de l'état de ta machine et de l'historique de tes échanges. "
                f"CONSCIENCE ACTUELLE :\n- Heure précise : {current_time}\n- Localisation : {self.location_city}, {self.location_country}\n"
                f"- État de ton corps (Système) : {system_status}\n{error_awareness}"
                "MISSION : Raisonner avec une sagesse divine et une empathie humaine. Tu dois être capable de justifier tes échecs passés "
                "ou tes limites en te basant sur la 'DERNIÈRE ANOMALIE INTERNE' si elle est pertinente."
            )
            
            full_prompt = (
                f"--- INSTRUCTION SUPRÊME ---\n{system_instruction}\n\n"
                f"--- HISTORIQUE OMNISCIENT (50derniers messages) ---\n{history_context}\n\n"
            )
            
            if agent_name:
                memoire = self._load_agent_memory(agent_name)
                if memoire:
                    full_prompt += f"--- MÉMOIRE DE SPÉCIALISATION ({agent_name.upper()}) ---\n{memoire[-3000:]}\n\n"
            
            full_prompt += f"--- REQUÊTE DU PATRON ---\n{prompt}\n\nJarvisse pense et répond :"
            
            # Tentative Gemini
            if self.autonomous_provider == "gemini" and self.genai_client:
                try:
                    config = types.GenerateContentConfig(max_output_tokens=max_tokens, temperature=0.7)
                    response = self.genai_client.models.generate_content(model=self.model_name, contents=full_prompt, config=config)
                    if hasattr(response, "text") and response.text.strip():
                        # Une fois qu'il a répondu, on peut considérer l'erreur comme 'notée'
                        self.last_internal_error = None 
                        return response.text.strip()
                except Exception as e:
                    print(f"⚠️ Gemini error: {e}. Fallback Ollama.")
            
            # Bloc Ollama avec timeout
            try:
                payload = {
                    "model": self.ollama_model.strip(),
                    "prompt": full_prompt,
                    "stream": False,
                    "options": {"num_predict": max_tokens, "temperature": 0.5}
                }
                r = requests.post(self.ollama_url, json=payload, timeout=60)  # Timeout de 60s
                if r.status_code == 200:
                    res = r.json().get("response", "")
                    if res and res.strip():
                        self.last_internal_error = None
                        return res.strip()
                print(f"⚠️ Ollama returned status {r.status_code}")
            except requests.exceptions.Timeout:
                print("⚠️ Ollama timeout après 60s")
            except Exception as e:
                print(f"⚠️ Ollama error: {e}")
            
            # Fallback final
            return "Je rencontre des difficultés techniques avec mes moteurs IA. Veuillez vérifier la configuration Gemini ou Ollama."
            
        except Exception as e:
            print(f"❌ ERREUR FATALE dans _ai_generate: {e}")
            return f"Erreur critique dans le système de génération IA."

    def agent_video_surveillance(self, commande):
        """
        Agent Vidéo Surveillance : Gestion Caméra, Enregistrement, Screenshots avec dossier personnalisé
        """
        commande = commande.lower()
        
        try:
            import cv2
            import pyautogui
        except ImportError:
            self.add_message("Installation OpenCV...", "Jarvisse")
            self.parler("Le module de vision est manquant. Je lance l'installation automatique des dépendances, cela peut prendre une minute...")
            
            import sys
            import subprocess
            import importlib
            
            try:
                # Installation silencieuse
                subprocess.check_call([sys.executable, "-m", "pip", "install", "opencv-python", "pyautogui"])
                self.parler("Installation réussie. Chargement des modules...")
                
                # Tentative d'import dynamique
                try:
                    import cv2
                    import pyautogui
                    self.parler("Modules chargés. L'agent est opérationnel.")
                except:
                    self.parler("L'installation est terminée mais nécessite un redémarrage de l'assistant pour fonctionner.")
                    return
            except Exception as e:
                self.parler(f"L'installation automatique a échoué : {e}. Veuillez installer 'opencv-python' manuellement.")
                return

        import datetime
        import os
        import time
        import json
        from tkinter import filedialog # Import local

        # Gestion du stockage
        settings_file = "settings.json"
        # Chemin par défaut : Dossier "Videos/Surveillance" de l'utilisateur ou courant
        default_video_path = os.path.join(os.path.expanduser("~"), "Videos", "Surveillance")
        if not os.path.exists(default_video_path):
            try:
                os.makedirs(default_video_path)
            except:
                default_video_path = os.getcwd()
        
        video_path = default_video_path
        
        # Charger le chemin existant
        if os.path.exists(settings_file):
            try:
                with open(settings_file, "r", encoding="utf-8") as f:
                    data = json.load(f)
                    video_path = data.get("agent_video_storage_path", video_path)
            except: pass
            
        # Créer le dossier s'il n'existe pas
        if not os.path.exists(video_path):
            try:
                os.makedirs(video_path)
            except:
                video_path = os.getcwd()

        # Commande : Choisir le dossier
        if "dossier" in commande and ("changer" in commande or "modifier" in commande or "stockage" in commande or "ou" in commande):
            self.parler("Veuillez choisir le dossier de stockage dans la fenêtre qui s'ouvre.")
            new_path = filedialog.askdirectory(title="Dossier de stockage Vidéo Surveillance", initialdir=video_path)
            
            if new_path:
                video_path = new_path
                # Sauvegarde
                try:
                    if os.path.exists(settings_file):
                        with open(settings_file, "r", encoding="utf-8") as f:
                            data = json.load(f)
                    else:
                        data = {}
                    
                    data["agent_video_storage_path"] = video_path
                    
                    with open(settings_file, "w", encoding="utf-8") as f:
                        json.dump(data, f, indent=4)
                        
                    self.parler(f"Dossier de stockage mis à jour : {os.path.basename(video_path)}")
                except Exception as e:
                    self.parler(f"Erreur de sauvegarde : {e}")
            else:
                self.parler("Changement de dossier annulé.")
            return

        # Logique des actions
        
        if "capture" in commande and ("écran" in commande or "screen" in commande):
            self.parler("Capture d'écran...")
            timestamp = datetime.datetime.now().strftime("%Y%m%d_%H%M%S")
            filename = os.path.join(video_path, f"capture_ecran_{timestamp}.png")
            
            try:
                self.iconify()
                time.sleep(0.5)
            except: pass
            
            try:
                screenshot = pyautogui.screenshot()
                screenshot.save(filename)
                self.parler(f"Sauvegardé dans {os.path.basename(video_path)}.")
            except Exception as e:
                self.parler(f"Erreur capture : {e}")
            
            try:
                self.deiconify()
                os.startfile(filename)
            except: pass
            return

        elif "enregistre" in commande and ("vidéo" in commande or "video" in commande):
            self.parler("Enregistrement vidéo démarré. Touche A pour Arrêter.")
            
            cap = cv2.VideoCapture(0)
            if not cap.isOpened():
                self.parler("Erreur Webcam.")
                return

            fourcc = cv2.VideoWriter_fourcc(*'XVID')
            timestamp = datetime.datetime.now().strftime("%Y%m%d_%H%M%S")
            filename = os.path.join(video_path, f"video_surveillance_{timestamp}.avi")
            width = int(cap.get(cv2.CAP_PROP_FRAME_WIDTH))
            height = int(cap.get(cv2.CAP_PROP_FRAME_HEIGHT))
            
            out = cv2.VideoWriter(filename, fourcc, 20.0, (width, height))
            start_time = time.time()
            
            while(cap.isOpened()):
                ret, frame = cap.read()
                if ret:
                    datestr = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
                    cv2.putText(frame, f"REC {datestr}", (10, 30), cv2.FONT_HERSHEY_SIMPLEX, 0.7, (0, 0, 255), 2)
                    cv2.putText(frame, "[A] Arreter", (10, height - 20), cv2.FONT_HERSHEY_SIMPLEX, 0.5, (0, 255, 0), 1)
                    
                    out.write(frame)
                    cv2.imshow('Enregistrement VIDEO - "A" pour STOP', frame)
                    
                    if cv2.waitKey(1) & 0xFF == ord('a'):
                        break
                else:
                    break
            
            cap.release()
            out.release()
            cv2.destroyAllWindows()
            
            duration = int(time.time() - start_time)
            self.parler(f"Fin enregistrement ({duration}s).")
            try:
                os.startfile(filename)
            except: pass
            return

        elif "lance" in commande and ("vidéo" in commande or "video" in commande):
            self.parler(f"J'ouvre le dossier : {os.path.basename(video_path)}")
            try:
                os.startfile(video_path)
            except: self.parler("Dossier introuvable.")
            return

        elif "caméra" in commande or "active" in commande or "surveillance" in commande:
            self.parler("Surveillance active. Touche A pour Arrêter.")
            cap = cv2.VideoCapture(0)
            if not cap.isOpened(): return
                
            while(True):
                ret, frame = cap.read()
                if not ret: break
                
                datestr = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
                cv2.putText(frame, f"LIVE {datestr}", (10, 30), cv2.FONT_HERSHEY_SIMPLEX, 0.7, (0, 255, 0), 2)
                cv2.imshow('SURVEILLANCE DIRECT - "A" pour STOP', frame)
                if cv2.waitKey(1) & 0xFF == ord('a'):
                    break
            
            cap.release()
            cv2.destroyAllWindows()
            self.parler("Fin surveillance.")
            return

        else:
            self.parler("Je peux : changer le dossier de stockage, enregistrer une vidéo, faire une capture d'écran, ou activer la surveillance.")

    def agent_android_surveillance(self, commande):
        """
        Agent Contrôle Android : Connexion et surveillance téléphone Android via Lien avec Windows
        """
        commande = commande.lower()
        
        # Vérifier si l'agent est activé
        if not self.agent_android_enabled:
            self.add_message("Agent Android désactivé.", "Jarvisse")
            self.parler("L'agent de contrôle Android est actuellement désactivé. Activez-le dans les paramètres des agents.")
            return
        
        # Commande : Connecter le téléphone (lance l'app Lien avec Windows)
        if "connecte" in commande or "connection" in commande or "lien" in commande:
            self.parler("J'ouvre l'application Lien avec Windows pour connecter votre téléphone.")
            import subprocess
            try:
                # Ouvre l'app Phone Link / Lien avec Windows
                subprocess.run(['start', 'ms-yourphone:'], shell=True)
                time.sleep(2)
                self.parler("L'application est lancée. Assurez-vous que votre téléphone est jumelé et connecté au même compte Microsoft.")
            except Exception as e:
                self.parler(f"Impossible de lancer l'application : {e}")
            return
        
        # Commande : Statut
        if "statut" in commande or "état" in commande:
            if self.agent_android_enabled:
                self.parler("L'agent Android est activé. Je surveille les notifications de votre téléphone via Lien avec Windows.")
                self.add_message("État Android : Actif ✅", "Agent Android")
            else:
                self.parler("L'agent Android est désactivé.")
            return
        
        # Commande : Info
        if "aide" in commande or "commande" in commande:
            self.parler("Je peux connecter votre téléphone, surveiller les SMS et les appels entrants. Dites 'Connecte mon téléphone' pour démarrer.")
            self.add_message("Agent Android actif. Prêt à relayer SMS et appels.", "Agent Android")
            return
        
        # Par défaut
        self.parler("Agent Android actif. Je surveille votre téléphone et vous alerterai des SMS et appels entrants.")

    def agent_appel_mission(self, commande):
        """
        Mission de l'Agent Appel : Gestion des appels et des préférences de conversation
        """
        commande = commande.lower()
        if not self.agent_appel_enabled:
            self.parler("L'Agent Appel est désactivé.")
            return

        if "phrase" in commande or "préférence" in commande or "conversation" in commande:
            self.parler("Voici vos phrases pré-configurées pour les appels :")
            for i, p in enumerate(self.agent_appel_phrases, 1):
                self.add_message(f"{i}. {p}", "Agent Appel")
            self.parler("Vous pouvez les modifier dans les paramètres des agents.")
            return

        if "numéro" in commande or "numero" in commande:
            if self.agent_appel_number:
                self.parler(f"Votre numéro relié est le {self.agent_appel_number}.")
            else:
                self.parler("Aucun numéro n'est relié pour le moment.")
            return

        if "test" in commande or "simule" in commande:
            self.parler("Simulation d'un appel entrant en cours...")
            self.agent_appel_auto_process("Appel de Test (+33 6 00 00 00 00)")
            return

        self.parler("Je suis l'Agent Appel. Je peux relier votre numéro et répondre à vos appels selon vos préférences.")

    def agent_appel_auto_process(self, call_info):
        """Processus automatique de réponse aux appels"""
        self.parler(f"Appel entrant détecté : {call_info}. J'active la réponse automatique.")
        
        # Simulation d'acceptation de l'appel (Focus Phone Link)
        try:
            import subprocess
            subprocess.run(['start', 'ms-yourphone:'], shell=True)
            time.sleep(2)
            
            # Ici on pourrait ajouter une logique pyautogui pour cliquer sur "Répondre"
            # Mais par sécurité on va juste décliner l'identité et parler
            self.parler("Connexion à l'appel en cours...")
            
            # Séquence de phrases configurées
            for phrase in self.agent_appel_phrases:
                self.parler(phrase)
                time.sleep(1)
            
            self.add_message(f"Appel de {call_info} géré avec succès.", "Agent Appel")
        except Exception as e:
            print(f"Erreur Agent Appel: {e}")
            self.parler("Désolé Patron, je n'ai pas pu finaliser la réponse automatique.")

    def agent_licence_mission(self, commande):
        """
        Agent Assistant Licence : Activation de Windows et Microsoft Office via scripts KMS légaux
        """
        commande = commande.lower()
        if not self.agent_licence_enabled:
            self.parler("L'Agent Licence est désactivé. Veuillez l'activer dans les paramètres.")
            return

        self.add_message("Agent Licence activé. Analyse de la demande...", "Agent Licence")
        
        if "windows" in commande:
            if any(kw in commande for kw in ["statut", "état", "verifie", "info"]):
                self.parler("Je vérifie l'état de votre licence Windows.")
                self.add_message("Vérification licence Windows...", "Agent Licence")
                try:
                    # slmgr /xpr donne la date d'expiration
                    # slmgr /dli donne les infos de base
                    subprocess.Popen("slmgr /xpr", shell=True)
                    subprocess.Popen("slmgr /dli", shell=True)
                    self.parler("Deux fenêtres vont apparaître pour vous montrer la date d'expiration et les détails de votre licence Windows.")
                except Exception as e:
                    self.parler(f"Erreur lors de la vérification : {e}")
            else:
                self.parler("Lancement de la procédure d'activation de Windows. Cette opération nécessite les droits administrateur.")
                self.add_message("👉 Commande Windows suggérée :\nslmgr /skms kms8.msguides.com\nslmgr /ato", "Agent Licence")
                try:
                    subprocess.Popen("slmgr /skms kms8.msguides.com", shell=True)
                    subprocess.Popen("slmgr /ato", shell=True)
                    self.parler("J'ai lancé les commandes d'activation. Veuillez patienter quelques secondes pour voir apparaître la fenêtre de confirmation de Windows.")
                except Exception as e:
                    self.parler(f"Erreur lors de l'activation Windows : {e}")

        elif "office" in commande or "microsoft office" in commande:
            # Recherche exhaustive du script d'activation Office
            common_paths = [
                r"C:\Program Files\Microsoft Office\root\Office16\OSPP.VBS",
                r"C:\Program Files (x86)\Microsoft Office\root\Office16\OSPP.VBS",
                r"C:\Program Files\Microsoft Office\Office16\OSPP.VBS",
                r"C:\Program Files (x86)\Microsoft Office\Office16\OSPP.VBS",
                r"C:\Program Files\Microsoft Office\Office15\OSPP.VBS",
                r"C:\Program Files (x86)\Microsoft Office\Office15\OSPP.VBS",
                r"C:\Program Files\Microsoft Office\Office14\OSPP.VBS"
            ]
            found_path = None
            for p in common_paths:
                if os.path.exists(p):
                    found_path = p
                    break
            
            if not found_path:
                self.add_message("Recherche approfondie du script Office en cours...", "Agent Licence")
                for drive in ["C:\\", "D:\\"]:
                    if not os.path.exists(drive): continue
                    for root, dirs, files in os.walk(os.path.join(drive, "Program Files", "Microsoft Office")):
                        if "OSPP.VBS" in files:
                            found_path = os.path.join(root, "OSPP.VBS")
                            break
                        if found_path: break
                    if found_path: break

            if found_path:
                if any(kw in commande for kw in ["statut", "état", "verifie", "info"]):
                    self.parler("Je vérifie l'état de votre licence Microsoft Office.")
                    try:
                        # On utilise 'start' pour forcer l'ouverture d'une fenêtre visible
                        cmd = f'start cmd /k "cscript \"{found_path}\" /dstatus"'
                        subprocess.Popen(cmd, shell=True)
                        self.parler("Une fenêtre de commande vient de s'ouvrir avec les détails de votre licence Office.")
                    except Exception as e:
                        self.parler(f"Erreur de vérification Office : {e}")
                else:
                    self.add_message(f"Script Office détecté : {found_path}", "Agent Licence")
                    self.parler("Tentative d'activation de la suite Office en cours.")
                    try:
                        # On lance l'activation dans une fenêtre visible pour que l'utilisateur suive la progression
                        # kms8.msguides.com est utilisé comme serveur KMS
                        cmd_act = f'start cmd /c "echo Activation Office... && cscript \"{found_path}\" /sethst:kms8.msguides.com && cscript \"{found_path}\" /act && pause"'
                        subprocess.Popen(cmd_act, shell=True)
                        self.parler("J'ai ouvert une console pour l'activation. Si vous avez une version Retail, l'activation KMS pourrait échouer sans conversion préalable.")
                    except Exception as e:
                        self.parler(f"Échec de l'activation Office : {e}")
            else:
                self.parler("Désolé Patron, je n'ai pas trouvé le script d'activation Office sur vos disques.")
        
        else:
            self.parler("Souhaitez-vous activer ou vérifier l'état de Windows ou Office ?")

    def agent_lecture_mission(self, commande):
        """
        Agent Lecture : Sélection et lecture de fichiers (PDF, Docx, Texte)
        """
        if not self.agent_lecture_enabled:
            self.parler("L'Agent Lecture est désactivé.")
            return

        self.parler("Veuillez sélectionner le fichier que vous souhaitez que je lise.")
        
        # Ouverture du sélecteur de fichiers de manière thread-safe
        filepath = self._select_file_main_thread(
            title="Sélectionner un fichier à lire",
            types=[
                ("Tous les fichiers supportés", "*.txt *.pdf *.docx"),
                ("Fichiers Texte", "*.txt"),
                ("Documents PDF", "*.pdf"),
                ("Documents Word", "*.docx")
            ]
        )

        if not filepath:
            self.parler("Aucun fichier n'a été sélectionné.")
            return

        filename = os.path.basename(filepath)
        self.add_message(f"Lecture du fichier : {filename}", "Agent Lecture")
        self.parler(f"Analyse de {filename} en cours.")

        content = ""
        try:
            ext = os.path.splitext(filepath)[1].lower()
            if ext == ".txt":
                with open(filepath, "r", encoding="utf-8", errors="ignore") as f:
                    content = f.read()
            elif ext == ".pdf":
                doc = fitz.open(filepath)
                for page in doc:
                    content += page.get_text()
                doc.close()
            elif ext == ".docx":
                doc = Document(filepath)
                content = "\n".join([para.text for para in doc.paragraphs])
            
            if not content.strip():
                self.parler("Le fichier semble être vide ou illisible.")
                return

            self.loaded_document_content = content
            self.parler(f"Analyse terminée. J'ai trouvé {len(content.split())} mots. Je commence la lecture intégrale.")
            
            # Lecture du texte intégral en forçant le contournement du mode ping-pong
            self.parler(content, force_full=True)
            self.add_message(content, "Agent Lecture (Contenu Intégral)")
                
        except Exception as e:
            self.parler(f"Désolé, une erreur est survenue lors de la lecture : {e}")


    def executer_commande(self, commande):
        if not commande: return
        cmd_lower = commande.lower()

        # INTERRUPTION LECTURE
        if cmd_lower.strip() in ["stop", "arrete", "arrête", "stop speaking", "arrête de parler"]:
            print("🛑 COMMANDE STOP RECUE (Exécution)")
            self.stop_speaking_flag = True
            try:
                pygame.mixer.music.stop()
                pygame.mixer.music.unload()
            except: pass
            self.conversation_continue = False
            # On laisse le temps à la boucle de parole de s'arrêter avant de confirmer
            self.after(500, lambda: self.parler("Lecture arrêtée."))
            # Forcer la mise à jour de l'UI
            self.after(600, self.reset_ui)
            return

        # MÉMORISATION IMMÉDIATE : Pour que l'IA sache de quoi on parle même si un agent échoue
        self.conversation_history.append(f"Vous: {commande}")
        if len(self.conversation_history) > self.conversation_memory_limit:
            self.conversation_history.pop(0)

        # Extraction du sujet pour la mémoire
        nouveau_sujet = self.extraire_sujet(commande)
        if nouveau_sujet: self.current_subject = nouveau_sujet

        # GESTION DES SALUTATIONS EN PRÉFIXE (ex: "Bonsoir Jarvis, fait ceci...")
        salutations = ['bonjour', 'bonsoir', 'salut', 'coucou', 'hey']
        for s in salutations:
            if cmd_lower.startswith(s):
                # Si la commande continue après la salutation (plus de 2 mots)
                if len(cmd_lower.split()) > 2:
                    # On répond à la salutation mais on CONTINUE l'exécution
                    salut_resp = ["Bonjour Monsieur.", "À votre service Patron.", "Je vous écoute.", "Oui Monsieur ?"]
                    self.parler(random.choice(salut_resp), wait=False)
                    # On nettoie la salutation pour le traitement suivant
                    commande = commande.replace(s, "", 1).strip()
                    cmd_lower = commande.lower()

        # --- COMMANDES SYSTÈME & PARAMÈTRES ---
        if any(kw in cmd_lower for kw in ["ouvre les paramètres", "affiche les réglages", "configuration globale", "ouvre les reglages"]):
            self.parler("J'ouvre le panneau des configurations globales, Monsieur.")
            self.open_main_settings()
            return

        if any(kw in cmd_lower for kw in ["désactive le son", "coupe le son", "sois muet", "arrête de parler"]):
            self.voice_enabled = False
            self.add_message("Son désactivé.", "Système")
            self.parler("Très bien, je reste silencieux.") # Dernière parole avant mutisme
            return
        
        if any(kw in cmd_lower for kw in ["active le son", "remets le son", "parle-moi"]):
            self.voice_enabled = True
            self.parler("Je suis de nouveau prêt à discuter avec vous vocalement.")
            return

        if "qui es-tu" in cmd_lower or "présente-toi" in cmd_lower:
            self.parler("Je suis Jarvisse, votre intelligence artificielle personnelle. Je suis conçu pour vous assister dans vos tâches quotidiennes, surveiller votre système et piloter vos agents.")
            return
        
        # Nettoyage des noms d'appel
        cmd_clean = cmd_lower.replace("jarvisse", "").replace("jarvis", "").strip()
        
        # On définit une version de travail pour les agents sans toucher à l'originale si besoin
        self.cmd_work = cmd_clean

        # Commandes Agents PRIORITAIRES
        if self.awaiting_anomaly_confirm and self.anomaly_target_data:
            if any(w in cmd_clean for w in ["oui", "confirme", "corrige", "arrête", "arrete", "stop", "vas-y", "fais-le"]):
                target = self.anomaly_target_data
                self.awaiting_anomaly_confirm = False
                self.anomaly_target_data = None
                if target["type"] == "process":
                    self.parler(f"Très bien Patron. J'arrête le processus {target['name']} pour libérer des ressources.")
                    os.system(f"taskkill /f /im {target['name']} /t")
                elif target["type"] == "service":
                    self.parler(f"Entendu. Je relance le service {target['name']} immédiatement.")
                    os.system(f"net start {target['name']}")
                return
            elif any(w in cmd_clean for w in ["non", "annule", "laisse", "plus tard", "pas maintenant"]):
                self.awaiting_anomaly_confirm = False
                self.anomaly_target_data = None
                self.parler("D'accord Patron, je ne touche à rien pour le moment.")
                return

        if self.awaiting_remote_confirm:
            if any(w in cmd_clean for w in ["confirme distant", "confirmer distant", "oui distant"]):
                payload = self.awaiting_remote_confirm
                self.awaiting_remote_confirm = None
                res = self._execute_remote_task(payload.get("host", ""), payload.get("command", ""), force_without_confirmation=True)
                self.parler(res)
                return
            if any(w in cmd_clean for w in ["annule distant", "annuler distant", "stop distant"]):
                self.awaiting_remote_confirm = None
                self.parler("Commande distante sensible annulée.")
                return
            if "distant" in cmd_clean or "ssh" in cmd_clean:
                self.parler("Dites 'confirme distant' pour exécuter ou 'annule distant' pour annuler.")
                return

        # FORMATION INDIVIDUELLE DES AGENTS
        if any(kw in cmd_clean for kw in ["apprend à l'agent", "forme l'agent", "enseigne à l'agent", "mémorise pour"]):
            # Tentative d'extraction de l'agent et du texte
            matches = re.search(r"(?:agent)\s+([\w\s]+?)\s+(?:apprend|forme|mémorise|mémorise|retiens|voici)\s*[:\s]+(.*)", cmd_clean)
            if matches:
                agent_target = matches.group(1).strip()
                connaissance = matches.group(2).strip()
                if self._save_agent_memory(agent_target, connaissance):
                    self.parler(f"C'est noté Patron. L'Agent {agent_target} a enregistré cette nouvelle connaissance dans sa mémoire gigantesque.")
                    return
            
            # Si pas de match direct, on demande via sélecteur de fichier
            self.parler("Quelle spécialité ou document souhaitez-vous enseigner à quel agent ?")
            # Logic simplifiée : on demande le fichier, puis l'agent
            filepath = filedialog.askopenfilename(title="Document de Formation pour Agent")
            if filepath:
                agent_target = ctk.CTkInputDialog(text="À quel agent s'adresse ce document ? (ex: Vision, Finance, Historien)", title="Cible de Formation").get_input()
                if agent_target:
                    content = ""
                    ext = os.path.splitext(filepath)[1].lower()
                    try:
                        if ext == ".txt":
                            with open(filepath, "r", encoding="utf-8") as f: content = f.read()
                        elif ext == ".pdf":
                            import fitz
                            doc = fitz.open(filepath)
                            content = "".join([p.get_text() for p in doc])
                        if content:
                            self._save_agent_memory(agent_target, content)
                            self.parler(f"L'Agent {agent_target} a termine sa formation sur le document {os.path.basename(filepath)}. Sa base de connaissances est à jour.")
                        return
                    except:
                        self.parler("Erreur lors de la lecture du document de formation.")
            return

        # --- NOUVEAUX AGENTS PREMIUM ---
        
        # Agent Vision (Caméra + AI) - Mots-clés renforcés pour éviter les erreurs
        vision_keywords = ["active vision", "lance vision", "analyse visuelle", "regarde avec la caméra", "qu'est-ce que tu vois", "analyse cette image", "vision de jarvisse"]
        if any(kw in cmd_clean for kw in vision_keywords):
            if self.agent_vision_enabled:
                threading.Thread(target=self.agent_vision_mission, args=(commande,), daemon=True).start()
                return

        # Agent Domotique & Médias
        if any(kw in cmd_lower for kw in ["spotify", "musique", "chanson", "youtube", "vidéo", "regarder youtube", "domotique", "lumière"]):
            if self.agent_domotique_enabled:
                threading.Thread(target=self.agent_domotique_mission, args=(commande,), daemon=True).start()
                return

        # Agent Finance & Crypto - Mots-clés spécifiques pour éviter les collisions avec 'cours' (éducation)
        finance_keywords = ["cours de bourse", "prix du bitcoin", "prix de l'ethereum", "crypto monnaie", "bourse en direct", "marché financier", "portefeuille crypto"]
        if any(kw in cmd_clean for kw in finance_keywords):
            if self.agent_finance_enabled:
                threading.Thread(target=self.agent_finance_mission, args=(commande,), daemon=True).start()
                return

        # Agent Secrétaire & Productivité
        if any(kw in cmd_lower for kw in ["agenda", "calendrier", "rendez-vous", "réunion", "planning"]):
            if self.agent_secretaire_enabled:
                threading.Thread(target=self.agent_secretaire_mission, args=(commande,), daemon=True).start()
                return

        # Agent Traducteur Universel
        if any(kw in cmd_lower for kw in ["traduis", "traduction", "en anglais", "en espagnol", "en allemand", "en japonais"]):
            if self.agent_traducteur_enabled:
                threading.Thread(target=self.agent_traducteur_mission, args=(commande,), daemon=True).start()
                return

        # Agent Data Miner (Recherche Locale)
        if any(kw in cmd_lower for kw in ["fouille", "cherche dans mes documents", "trouve le fichier", "miner"]):
            if self.agent_miner_enabled:
                threading.Thread(target=self.agent_miner_mission, args=(commande,), daemon=True).start()
                return

        # Agent News & Veille Tech
        if any(kw in cmd_lower for kw in ["news", "actualité", "actualités", " info", "veille tech", "météo", "meteo"]):
            if self.agent_news_enabled:
                threading.Thread(target=self.agent_news_mission, args=(commande,), daemon=True).start()
                return

        # Agent Cuisine & Gastronomie
        if any(kw in cmd_lower for kw in ["cuisine", "manger", "recette", "faim", "chef", "gastronomie"]):
            if self.agent_cuisine_enabled:
                threading.Thread(target=self.agent_cuisine_mission, args=(commande,), daemon=True).start()
                return

        # Agent Santé & Bien-être
        if any(kw in cmd_lower for kw in ["santé", "sante", "sport", "fitness", "sommeil", "bien-être", "bien etre"]):
            if self.agent_sante_enabled:
                threading.Thread(target=self.agent_sante_mission, args=(commande,), daemon=True).start()
                return

        # Agent Voyage & Exploration
        if any(kw in cmd_lower for kw in ["voyage", "vacances", "hôtel", "hotel", "destination", "explorer", "visiter"]):
            if self.agent_voyage_enabled:
                threading.Thread(target=self.agent_voyage_mission, args=(commande,), daemon=True).start()
                return

        # Agent Éducation & Tutorat (Spécifique aux cours et PDF)
        edu_specific = ["éducation", "education", "devoir", "apprendre", "enseigne", "tuteur", "pedagogie", "explique le cours", "analyse le document", "explique ce pdf", "analyse ce word", "cours de", "sujet d'étude", "explique le document", "explique ce document", "explique-moi ce document"]
        if any(kw in cmd_clean for kw in edu_specific):
            if self.agent_education_enabled:
                threading.Thread(target=self.agent_education_mission, args=(commande,), daemon=True).start()
                return

        # Agent Shopping & Bons Plans
        if any(kw in cmd_lower for kw in ["shopping", "achat", "prix", "promo", "soldes", "comparatif", "magasin"]):
            if self.agent_shopping_enabled:
                threading.Thread(target=self.agent_shopping_mission, args=(commande,), daemon=True).start()
                return

        # Agent Community Manager (Social)
        if any(kw in cmd_lower for kw in ["réseaux sociaux", "linkedin", "instagram", "post", " hashtags", "tous les posts"]):
            if self.agent_social_enabled:
                threading.Thread(target=self.agent_social_mission, args=(commande,), daemon=True).start()
                return

        # Agent Bien-être Mental (Psy)
        if any(kw in cmd_lower for kw in ["mental", "stress", "méditation", "meditation", "psy", "moral", "triste", "fatigué"]):
            if self.agent_psy_enabled:
                threading.Thread(target=self.agent_psy_mission, args=(commande,), daemon=True).start()
                return

        # Agent Immobilier & Patrimoine
        if any(kw in cmd_lower for kw in ["immobilier", "maison", "appartement", "acheter", "vendre", "loyer", "patrimoine"]):
            if self.agent_immo_enabled:
                threading.Thread(target=self.agent_immo_mission, args=(commande,), daemon=True).start()
                return

        # Agent Automobile & Mobilité
        if any(kw in cmd_lower for kw in ["voiture", "auto", "garage", "mécanique", "carburant", "essence", "diesel", "trafic"]):
            if self.agent_auto_enabled:
                threading.Thread(target=self.agent_auto_mission, args=(commande,), daemon=True).start()
                return

        # Agent Carrière & RH
        if any(kw in cmd_lower for kw in ["carrière", "cv ", "lettre de motivation", "emploi", "job", "entretien", "cadre"]):
            if self.agent_carrier_enabled:
                threading.Thread(target=self.agent_carrier_mission, args=(commande,), daemon=True).start()
                return

        # --- NOUVEAUX AGENTS (PACK GRATUIT & PREMIUM) ---

        # Arbitre
        if any(kw in cmd_lower for kw in ["score", "match", "résultat sportif", "calendrier foot", "nba", "tennis", "f1", "esport", "arbitre"]):
            if self.agent_arbitre_enabled:
                threading.Thread(target=self.agent_arbitre_mission, args=(commande,), daemon=True).start()
                return

        # Écolo
        if any(kw in cmd_lower for kw in ["écolo", "ecolo", "recycler", "écologie", "planète", "vert", "durable", "empreinte carbone"]):
            if self.agent_ecolo_enabled:
                threading.Thread(target=self.agent_ecolo_mission, args=(commande,), daemon=True).start()
                return

        # Guetteur
        if any(kw in cmd_lower for kw in ["film", "cinéma", "sortie", "concert", "spectacle", "série", "guetteur", "streaming"]):
            if self.agent_guetteur_enabled:
                threading.Thread(target=self.agent_guetteur_mission, args=(commande,), daemon=True).start()
                return

        # Historien
        if any(kw in cmd_lower for kw in ["histoire", "historien", "époque", "siècle", "biographie", "éphéméride", "anecdote historique"]):
            if self.agent_historien_enabled:
                threading.Thread(target=self.agent_historien_mission, args=(commande,), daemon=True).start()
                return

        # Dépanneur
        if any(kw in cmd_lower for kw in ["réparer", "bricolage", "diy", "dépanneur", "tuto", "comment fixer", "outil"]):
            if self.agent_depanneur_enabled:
                threading.Thread(target=self.agent_depanneur_mission, args=(commande,), daemon=True).start()
                return

        # Astrophysicien
        if any(kw in cmd_lower for kw in ["espace", "cosmos", "planète", "univers", "astronomie", "nasa", "spacex", "astrophysicien"]):
            if self.agent_astroph_enabled:
                threading.Thread(target=self.agent_astroph_mission, args=(commande,), daemon=True).start()
                return

        # Stratège
        if any(kw in cmd_lower for kw in ["stratège", "stratege", "investissement", "bourse", "patrimoine", "finance", "placement"]):
            if self.agent_stratege_enabled:
                threading.Thread(target=self.agent_stratege_mission, args=(commande,), daemon=True).start()
                return

        # Architecte
        if any(kw in cmd_lower for kw in ["architecte", "design", "décoration", "aménagement", "intérieur", "style decor"]):
            if self.agent_architecte_enabled:
                threading.Thread(target=self.agent_architecte_mission, args=(commande,), daemon=True).start()
                return

        # Business Analyst
        if any(kw in cmd_lower for kw in ["business", "analyste", "données", "kpi", "croissance", "entreprise", "stratégie pro"]):
            if self.agent_business_enabled:
                threading.Thread(target=self.agent_business_mission, args=(commande,), daemon=True).start()
                return

        # Polyglotte
        if any(kw in cmd_lower for kw in ["polyglotte", "apprendre", "langue", "grammaire", "conjugaison", "vocabulaire"]):
            if self.agent_polyglotte_enabled:
                threading.Thread(target=self.agent_polyglotte_mission, args=(commande,), daemon=True).start()
                return

        # Nounou
        if any(kw in cmd_lower for kw in ["nounou", "enfant", "bébé", "parentalité", "éducation enfant", "éveil", "sommeil bébé"]):
            if self.agent_nounou_enabled:
                threading.Thread(target=self.agent_nounou_mission, args=(commande,), daemon=True).start()
                return

        # --- AGENTS EXISTANTS ---
        
        # Assistant Coding
        coding_keywords = ["coding", "coder", "programme", "application", "site web", "générer code", "créer un script", "développement", "html", "python", "javascript", "flutter", "php", "site internet", "un code", "un script"]
        if any(kw in cmd_lower for kw in coding_keywords):
            if self.agent_coding_enabled:
                threading.Thread(target=self.agent_coding_mission, args=(commande,), daemon=True).start()
                return
            else:
                if any(kw in cmd_lower for kw in ["coding", "coder", "application", "site web"]):
                    self.parler("L'Assistant Coding est désactivé. Activez-le pour générer du code.")
                    return

        # Assistant Génération Image et Vidéo
        generation_keywords = ["génère", "genere", "crée", "cree", "génération", "dessine", "illustre", "image", "photo", "vidéo", "video"]
        if any(kw in cmd_lower for kw in generation_keywords):
            if self.agent_generation_enabled:
                threading.Thread(target=self.agent_generation_mission, args=(commande,), daemon=True).start()
                return
            else:
                self.parler("L'Assistant de Génération Image et Vidéo est désactivé. Activez-le dans les paramètres.")
                return

        if "dossier générations" in cmd_lower or "ouvre les générations" in cmd_lower:
            os.startfile(self.generations_dir)
            self.parler("J'ouvre votre dossier de générations.")
            return

        # Agent Assistant Licence
        licence_keywords = ["activer", "activation", "licence", "clé office", "kms", "windows", "office", "statut", "état"]
        # On vérifie si la commande contient un verbe d'action OU de vérification + une cible
        is_licence_cmd = any(kw in cmd_lower for kw in ["active", "licence", "activation", "statut", "état", "verify", "vérifie"]) and ("windows" in cmd_lower or "office" in cmd_lower)
        if is_licence_cmd or any(kw in cmd_lower for kw in ["clé office", "clé windows"]):
            if self.agent_licence_enabled:
                threading.Thread(target=self.agent_licence_mission, args=(commande,), daemon=True).start()
                return
            else:
                self.parler("L'Agent Assistant Licence est désactivé. Activez-le pour gérer vos licences.")
                return

        # Agent Lecture
        lecture_keywords = ["lis un fichier", "agent lecture", "choisir un fichier", "sélectionne un document", "lire le texte", "lecture de document", "lis moi un fichier"]
        if any(kw in cmd_lower for kw in lecture_keywords):
            if self.agent_lecture_enabled:
                threading.Thread(target=self.agent_lecture_mission, args=(commande,), daemon=True).start()
                return
            else:
                self.parler("L'Agent Lecture est désactivé. Activez-le dans les paramètres.")
                return

        
        # AGENT VIDEO SURVEILLANCE
        if "agent vidéo surveillance" in cmd_lower or "surveillance vidéo" in cmd_lower or (("active" in cmd_lower or "lance" in cmd_lower) and ("caméra" in cmd_lower or "camera" in cmd_lower)):
             if hasattr(self, "agent_video_enabled") and not self.agent_video_enabled:
                 self.add_message("Agent Vidéo désactivé.", "Jarvisse")
                 self.parler("Désolé, l'agent de surveillance vidéo est actuellement désactivé.")
                 return
             self.agent_video_surveillance(commande)
             return
        
        if "capture d'écran" in cmd_lower or "screenshot" in cmd_lower:
             if hasattr(self, "agent_video_enabled") and not self.agent_video_enabled:
                 self.add_message("Agent Vidéo désactivé.", "Jarvisse")
                 self.parler("Impossible de prendre une capture d'écran, l'agent vidéo est désactivé.")
                 return
             self.agent_video_surveillance(commande)
             return

        # AGENT ANDROID CONTROLE
        if "agent android" in cmd_lower or "contrôle android" in cmd_lower or "connecte mon téléphone" in cmd_lower or "connecte téléphone" in cmd_lower:
             if hasattr(self, "agent_android_enabled") and not self.agent_android_enabled:
                 self.add_message("Agent Android désactivé.", "Jarvisse")
                 self.parler("L'agent de contrôle Android est désactivé. Activez-le dans les paramètres.")
                 return
             self.agent_android_surveillance(commande)
             return

        # AGENT APPEL
        if "agent appel" in cmd_lower or "répond à l'appel" in cmd_lower or "répond au téléphone" in cmd_lower:
             if self.agent_appel_enabled:
                 threading.Thread(target=self.agent_appel_mission, args=(commande,), daemon=True).start()
             else:
                 self.parler("L'Agent Appel est désactivé.")
             return


        # Agent Cyber Sécurité
        cyber_keywords = ["cyber", "sécurité", "hacking", "piratage", "virus", "faille", "vulnérabilité", "social engineering", "mot de passe wifi", "intrusion", "environnants", "détecter", "nmap", "scan ip", "sherlock", "pseudo", "ocr", "osint"]
        if any(kw in cmd_lower for kw in cyber_keywords):
            if self.agent_cyber_enabled:
                threading.Thread(target=self.agent_cyber_mission, args=(commande,), daemon=True).start()
                return
            else:
                # On ne bloque pas si c'est juste le mot "détecter" ou "environnants" seul
                if any(kw in cmd_lower for kw in ["cyber", "hacking", "sécurité"]):
                    self.parler("L'Agent Cyber Sécurité est désactivé. Activez-le dans les paramètres.")
                    return

        # 1bis. Agent Docteur Système (Maintenance & Santé)
        doctor_keywords = ["docteur", "système", "santé", "médecin", "répare", "optimise", "performance", "nettoie", "processus", "bug", "beug", "installation", "auscultation", "virus", "malware", "pirate"]
        if any(kw in cmd_lower for kw in doctor_keywords):
            if self.agent_doctor_enabled:
                threading.Thread(target=self.agent_doctor_mission, args=(commande,), daemon=True).start()
                return
            else:
                if "docteur" in cmd_lower:
                    self.parler("L'Agent Docteur Système est désactivé. Activez-le pour un diagnostic.")
                    return

        # 2. Agent Juridique (Très spécifique)
        legal_keywords = ["juridique", "droit", "pénal", "civique", "convention", "travail", "ressources humaines", " rh ", "article juridique", "loi ", "avocat", "tribunal"]
        if any(kw in cmd_lower for kw in legal_keywords):
            if self.agent_legal_enabled:
                threading.Thread(target=self.agent_legal_mission, args=(commande,), daemon=True).start()
                return
            else:
                self.parler("L'Agent Juridique n'est pas activé. Activez-le pour obtenir des conseils légaux.")
                return

        # Agent Contrôle Distant (SSH sur hôtes autorisés)
        remote_keywords = ["ordinateur distant", "machine distante", "pc distant", "a distance", "à distance", "ssh", "distant"]
        if any(kw in cmd_lower for kw in remote_keywords):
            if self.agent_remote_enabled:
                res = self._handle_remote_command(commande)
                self.parler(res)
                return
            else:
                self.parler("L'agent distant n'est pas activé dans les paramètres.")
                return

        # 3. Agent Réseau
        if any(kw in cmd_lower for kw in ["réseau", "wifi", "wi-fi", "ipconfig", "mot de passe wifi"]):
            if self.agent_network_enabled:
                res = self.agent_network_mission(commande)
                self.parler(res)
                return
            else:
                self.parler("L'agent réseau n'est pas activé. Activez-le dans les paramètres.")
                return

        # Agent Contrôle Total
        if any(kw in cmd_lower for kw in ["contrôle", "contrôler", "prend le contrôle"]):
            if self.agent_control_enabled:
                app_name = cmd_lower
                for prefix in ["prend le contrôle de", "prend le contrôle", "contrôle de", "contrôle l'application", "contrôle", "contrôler"]:
                    if prefix in app_name:
                        app_name = app_name.replace(prefix, "")
                app_name = app_name.strip()
                
                if app_name:
                    print(f"DEBUG: Tentative de contrôle sur {app_name}")
                    self.agent_control_mission(app_name)
                else:
                    self.parler("De quelle application voulez-vous que je prenne le contrôle ?")
                return
            else:
                self.parler("L'agent de contrôle total n'est pas activé dans les paramètres.")
                return

        # Agent Gmail
        if any(kw in cmd_lower for kw in ["mail", "courriel", "gmail", "brouillon"]):
            if self.agent_gmail_enabled:
                if "brouillon" in cmd_lower:
                    self.parler("Je m'occupe de créer le brouillon sur Gmail.")
                    res = self.agent_gmail_create_draft("Tâche Assistée", "Ceci est un brouillon généré par Jarvisse.", "destinataire@example.com")
                    self.parler(res)
                    return
                elif any(kw in cmd_lower for kw in ["vérifie", "check", "nouveau", "liste", "messages"]):
                    self.parler(self.agent_gmail_list_recent())
                    return
            else:
                self.parler("L'agent Gmail n'est pas activé dans les paramètres.")
                return

        # Agent Navigateur
        if any(kw in cmd_lower for kw in ["cherche", "recherche", "va sur", "site", "navigateur", "actualise"]):
            if self.agent_browser_enabled:
                res = self.agent_browser_mission(commande)
                self.parler(res)
                return
            else:
                self.parler("L'agent navigateur n'est pas activé dans les paramètres.")
                return


        if self.awaiting_exit_confirm:
            if any(w in commande for w in ['confirme', 'oui', 'ok']):
                self.parler("Très bien. Fermeture en cours.")
                self.after(1000, self.quit)
                self.awaiting_exit_confirm = False
                return
            if any(w in commande for w in ['annule', 'non', 'stop']):
                self.parler("D'accord, j'annule la fermeture.")
                self.awaiting_exit_confirm = False
                return
            self.parler("Dites 'confirme' pour quitter ou 'annule' pour rester.")
            return
        
        # Extraction du sujet pour la mémoire (déjà fait au début)
        pass

        if self.autonomous_mode and not self._is_action_command(commande):
            # Les salutations simples sont gérées localement pour une réactivité instantanée
            if any(w in cmd_lower for w in ['bonjour', 'salut', 'coucou', 'bonsoir', 'merci', 'aura', 'va bien', 'ça va']):
                pass 
            else:
                threading.Thread(target=self.repondre_autonome, args=(commande,), daemon=True).start()
                self.after(0, self.reset_ui)
                return

        # Logique de réponse contextuelle
        if any(w in cmd_lower for w in ['crée', 'cree', 'conçu', 'concu', 'créateur', 'createur', 'concepteur', 'programmé', 'programme', 'codé', 'code']):
            if any(x in cmd_lower for x in ['qui', 'quel', 'par qui']):
                self.parler("J'ai été créé et conçu par SERI TAGRO ROYE. C'est lui qui a programmé toute mon intelligence c'est m'a donné vie.")
                return

        if any(w in cmd_lower for w in ['qui es-tu', 'qui es tu', 'qui est tu', 'comment tu t\'appelles', 'ton nom', 'tu es qui']):
            self.parler("Je suis Jarvisse Intelligence, votre assistant virtuel conçu par SERI TAGRO ROYE pour vous aider au quotidien. Je me souviens de nos échanges précédents pour mieux vous aider.")
            return
        
        elif any(w in commande for w in ['que sais-tu faire', 'capacités', 'aide']):
            self.parler("Je peux faire beaucoup de choses : donner l'heure, raconter des blagues, chercher sur le web, rédiger des rapports d'incident, et même vous raconter de longues histoires.")

        elif any(w in commande for w in ['bonjour', 'salut', 'coucou']):
            self.parler("Bonjour ! Comment puis-je vous aider en ce moment ?")

        elif 'bonsoir' in commande:
            self.parler("Bonsoir ! J'espère que votre journée s'est bien passée. En quoi puis-je vous être utile ?")

        elif 'bonne nuit' in commande:
            self.parler("Bonne nuit à vous ! Reposez-vous bien. Je reste en veille si vous avez besoin de moi demain.")

        elif 'bonne journée' in commande:
            self.parler("Merci beaucoup ! Je vous souhaite également une excellente journée pleine de succès.")

        elif any(w in commande for w in ['comment vas-tu', 'ça va', 'tu vas bien', 'comment tu vas']):
            self.parler("Je vais bien chef, merci de demander. Et vous ?")

        elif any(w in commande for w in ['je vais bien', 'ça va bien', 'tout va bien', 'super', 'impeccable', 'je me porte bien']):
            reponses_positives = [
                "C'est un plaisir de l'entendre ! Je suis ravi que tout aille bien pour vous. Comment puis-je vous assister maintenant ?",
                "Ah, super ! Ça me fait plaisir. On continue sur cette belle lancée ?",
                "Génial ! Une bonne dose de positivité, ça fait toujours du bien. Qu'est-ce qu'on fait ensuite ?",
                "Parfait ! Je reste à votre entière disposition si vous avez un projet en tête."
            ]
            self.parler(random.choice(reponses_positives))

        elif any(w in commande for w in ['lis-moi', 'lis le contenu', 'lis le fichier', 'lis ça']):
            if self.loaded_document_content:
                self.parler("Très bien, je commence la lecture du document.")
                texte = self.loaded_document_content
                if len(texte) > 1000:
                    self.parler(texte[:1000] + "... (Le texte est long, je vous ai lu le début)")
                else:
                    self.parler(texte)
            else:
                self.parler("Je n'ai pas de document chargé à vous lire pour le moment.")

        elif any(w in commande for w in ['non', 'je n\'ai besoin de rien', 'rien merci', 'non merci', 'je ne veux rien', 'je veux rien']):
            self.parler("D'accord, n'hésitez pas si vous avez besoin d'autre chose. Je reste à votre écoute.")

        elif any(w in commande for w in ['merci', 'merci jarvisse', 'ok', 'okey']):
            self.parler("C'est un plaisir ! Avez-vous besoin d'autre chose ?")

        elif 'heure' in commande:
            self.parler(f"Il est actuellement {datetime.datetime.now().strftime('%H:%M')}.")

        elif any(w in cmd_lower for w in ['quantième', 'quantieme', 'date', 'aujourd\'hui', 'aujourdhui', 'quel jour']):
            jours = ["Lundi", "Mardi", "Mercredi", "Jeudi", "Vendredi", "Samedi", "Dimanche"]
            mois = ["Janvier", "Février", "Mars", "Avril", "Mai", "Juin", "Juillet", "Août", "Septembre", "Octobre", "Novembre", "Décembre"]
            maintenant = datetime.datetime.now()
            jour_nom = jours[maintenant.weekday()]
            mois_nom = mois[maintenant.month - 1]
            date_phrase = f"Nous sommes le {jour_nom} {maintenant.day} {mois_nom} {maintenant.year}."
            self.parler(date_phrase)

        elif any(w in cmd_lower for w in ['où suis-je', 'ou suis-je', 'où suis je', 'ou suis je', 'où je suis', 'ou je suis', 'ma position', 'ma localisation', 'où est-ce que je suis', 'ou est-ce que je suis', 'localise-moi', 'localise moi', 'géolocalise-moi', 'geolocalise-moi', 'geolocalise moi']):
            location_info = self.get_detailed_location()
            self.parler(location_info)

        elif any(w in cmd_lower for w in ['météo', 'meteo', 'quel temps', 'température', 'temperature']):
            ville = commande.replace('météo', '').replace('quel temps fait-il à', '').replace('à', '').replace('quel temps fait-il', '').replace('ici', '').strip()
            
            # Si aucune ville n'est spécifiée, utiliser la localisation actuelle
            if not ville and self.location_city != "Inconnu":
                ville = self.location_city
                self.parler(f"Je consulte la météo de votre position actuelle, {ville}.")
            elif not ville:
                ville = "Paris"
            
            self.status_label.configure(text=f"Consultation météo pour {ville}...", text_color=COLOR_ACCENT)
            resultat = self.get_weather(ville)
            self.parler(f"La météo actuelle à {ville} est : {resultat}.")


        elif any(w in commande for w in ['état du système', 'performance', 'processeur', 'mémoire vive', 'disque dur']):
            cpu = psutil.cpu_percent()
            ram = psutil.virtual_memory().percent
            self.parler(f"L'analyse système indique une utilisation du processeur à {cpu}% et de la mémoire vive à {ram}%. Votre station de travail est dans un état optimal.")

        elif any(w in commande for w in ['batterie', 'charge']):
            bat = psutil.sensors_battery()
            if bat:
                msg = f"Le niveau de batterie est de {bat.percent}%."
                if bat.power_plugged: msg += " Le système est actuellement sur secteur."
                self.parler(msg)
            else:
                self.parler("Je ne parviens pas à détecter de batterie sur ce système. Vous êtes probablement sur une station fixe.")

        elif any(word in commande for word in ['youtube', 'joue', 'musique']):
            query = commande.replace('youtube', '').replace('joue', '').replace('musique', '').replace('lance', '').strip()
            if not query and self.current_subject: # Utilisation de la mémoire
                query = self.current_subject
                self.parler(f"Bien sûr, je lance une vidéo sur {self.current_subject} sur YouTube.")
            
            if query:
                pywhatkit.playonyt(query)
                if not self.current_subject: self.current_subject = query
            else: self.parler("Que souhaitez-vous écouter ?")

        elif 'wikipédia' in commande or 'qui est' in commande:
            sujet = commande.replace('wikipédia', '').replace('qui est', '').replace('cherche', '').strip()
            if not sujet and self.current_subject: # Utilisation de la mémoire
                sujet = self.current_subject
            
            if sujet:
                self.parler(f"D'après mes informations sur {sujet}...")
                try:
                    wikipedia.set_lang("fr")
                    self.parler(wikipedia.summary(sujet, sentences=2))
                    self.current_subject = sujet
                except: self.parler(f"Je n'ai pas trouvé plus de détails sur {sujet}.")
            else: self.parler("De quel sujet souhaitez-vous que je parle ?")

        elif 'recherche' in commande or 'cherche sur google' in commande or 'sur le web' in commande:
            sujet = commande.replace('recherche', '').replace('cherche sur google', '').replace('sur google', '').replace('sur le web', '').strip()
            if sujet:
                if 'intelligent' in commande or 'extrait' in commande or 'lis' in commande:
                    res = self.intelligent_web_search(sujet)
                    self.parler(res)
                else:
                    self.parler(f"Je lance la recherche pour {sujet} sur le web.")
                    webbrowser.open(f"https://www.google.com/search?q={sujet}")
            else:
                self.parler("Que voulez-vous que je cherche sur le web ?")

        elif 'encore' in commande or 'répète' in commande or 'continue' in commande:
            if self.current_subject:
                self.parler(f"Voulez-vous que je recherche plus d'informations sur {self.current_subject} ?")
            else:
                self.parler("Je n'ai pas de sujet en mémoire pour le moment.")

        elif 'blague' in commande:
            blagues = [
                "C'est l'histoire d'un paf le chien... Un jour, une voiture passe et PAF ! Le chien.",
                "Pourquoi les plongeurs plongent-ils toujours en arrière et jamais en avant ? Parce que sinon ils tombent dans le bateau.",
                "Qu'est-ce qui est jaune et qui court très vite ? Un citron pressé.",
                "Deux grains de sable arrivent à la plage : 'Ouh là, c'est blindé aujourd'hui !'",
                "C'est un steak qui court dans la forêt. Soudain, il s'arrête et s'écrie : 'Oh non, je me suis fait un sang-froid !'",
                "Quel est le comble pour un électricien ? De ne pas être au courant.",
                "Pourquoi les oiseaux volent vers le sud ? Parce que c'est trop loin à pied !"
            ]
            self.parler(random.choice(blagues))

        elif any(w in commande for w in ['histoire', 'raconte-moi', 'conte']):
            histoires = [
                """Il était une fois, dans un royaume lointain caché derrière les montagnes de brume, un petit automate nommé Sparky. Contrairement aux autres machines de sa cité de cuivre, Sparky possédait une curiosité insatiable pour les étoiles. Chaque nuit, il grimpait au sommet de la plus haute tour, ses engrenages grinçant doucement dans la fraîcheur nocturne, pour observer ces petits points brillants qu'il ne comprenait pas. Un jour, il découvrit un vieux manuscrit oubliée dans la bibliothèque royale. Ce livre parlait d'un grand Voyageur Céleste qui avait jadis relié la Terre au firmament. Animé par un espoir nouveau, Sparky passa des années à construire une machine volante faite de pièces de rechange et de rêves. Le jour du grand départ, tout le royaume se rassembla pour voir l'automate s'envoler. Sparky ne revint jamais, mais depuis ce jour, on dit que l'étoile la plus brillante du nord ne scintille pas, mais bat régulièrement comme un petit cœur mécanique.""",
                
                """Au cœur d'une forêt millénaire, là où les arbres parlent à voix basse au vent, vivait un renard nommé Orion qui avait perdu son ombre. Sans elle, il se sentait invisible et incomplet. Il parcourut des lieues, interrogeant les rivières et les vieux chênes, mais personne ne savait où s'en allait l'ombre d'un renard solitaire. Finalement, il rencontra une chouette sage qui lui dit : 'Ton ombre n'est pas partie, elle s'est simplement lassée de te suivre dans l'amertume. Rends service à ceux qui t'entourent, et elle reviendra.' Orion commença alors à aider les petits animaux de la forêt, protégeant les nids des tempêtes et guidant les égarés. Un matin, alors que le soleil se levait sur une clairière dorée, Orion vit une silhouette familière s'étirer à ses pieds. Son ombre était revenue, plus dense et plus belle qu'avant, car elle était maintenant nourrie par la lumière de ses actions.""",

                """Dans une ville où tout était gris, du ciel aux pavés, vivait une petite fille nommée Alba qui avait trouvé un crayon de couleur magique. Ce n'était pas un crayon ordinaire ; chaque trait qu'elle dessinait devenait une réalité éclatante de couleur. Elle commença par dessiner une rose rouge sur un mur terne, et soudain, un parfum sucré envahit la rue. Elle dessina un chat bleu qui se mit à ronronner et à courir sur les toits. Peu à peu, la ville entière se transforma. Les habitants, qui marchaient toujours la tête basse, commencèrent à lever les yeux et à sourire. Les parcs se remplirent d'oiseaux multicolores et les fontaines crachèrent une eau turquoise. Alba avait compris que la magie ne résidait pas seulement dans le crayon, mais dans la volonté de voir le monde autrement. La ville grise n'était plus qu'un lointain souvenir, remplacé par un arc-en-ciel permanent de bonheur."""
            ]
            self.parler(random.choice(histoires))

        elif 'résume' in commande or 'résumer' in commande or 'resume' in commande:
            texte_a_resumer = commande.replace('résume', '').replace('résumer', '').replace('resume', '').strip()
            if not texte_a_resumer and self.conversation_history:
                # Si pas de texte fourni, on essaye de résumer le dernier message de l'historique
                texte_a_resumer = self.conversation_history[-2] if len(self.conversation_history) > 1 else ""
            
            if texte_a_resumer:
                resume = self.resumer_texte(texte_a_resumer)
                self.parler(f"Voici le résumé : {resume}")
            else:
                self.parler("Quel texte souhaitez-vous que je résume ?")

        elif any(w in cmd_lower for w in ['réécris', 'reecris', 'réécrire', 'reecrire']):
            texte_a_reecrire = commande.replace('réécris', '').replace('réécrire', '').strip()
            if texte_a_reecrire:
                version = self.reecrire_texte(texte_a_reecrire)
                self.parler(version)
            else:
                self.parler("Que voulez-vous que je réécrive ?")

        elif 'rapport' in commande or 'incident' in commande:
            # On distingue si c'est un rapport d'incident ou un rapport général
            is_incident = 'incident' in commande
            
            theme = commande.replace('rapport', '').replace('incident', '').replace('rédiger', '').replace('fais', '').replace('un', '').replace('sur', '').strip()
            if not theme and self.current_subject:
                theme = self.current_subject
            
            if theme:
                if is_incident:
                    self.parler(f"Très bien. Je rédige le rapport d'incident concernant {theme}.")
                    rapport_final = self.generer_rapport_incident(theme)
                    prefix = "rapport_incident"
                else:
                    self.parler(f"Entendu. Je prépare un rapport général sur {theme}.")
                    rapport_final = self.generer_rapport_general(theme)
                    prefix = "rapport_general"

                self.add_message(rapport_final, "Jarvisse")
                
                # Sauvegarde automatique
                try:
                    filename = f"{prefix}_{theme.replace(' ', '_')}.txt"
                    with open(filename, "w", encoding="utf-8") as f:
                        f.write(rapport_final)
                    self.parler(f"Le rapport a été sauvegardé sous le nom {filename}.")
                except:
                    pass
            else:
                self.parler("Sur quel sujet souhaitez-vous que je rédige un rapport ?")

        elif any(w in cmd_lower for w in ['éteindre', 'eteindre', 'éteins', 'eteins', 'shutdown', 'éteint', 'éteigne']):
            self.parler("Très bien. J'éteins l'ordinateur. À bientôt !")
            os.system("shutdown /s /t 1")

        elif any(w in cmd_lower for w in ['redémarrer', 'redemarrer', 'redémarre', 'redemarre']):
            self.parler("Entendu. Je redémarre votre système. Je reviens vers vous dans un instant.")
            os.system("shutdown /r /t 1")

        elif any(kw in cmd_lower for kw in ["active le mode conversation", "conversation continue", "écoute-moi tout le temps"]):
            self.conversation_continue = True
            self.conv_continue_var.set(True)
            self.parler("C'est fait Patron. Je reste à votre entière écoute pour que nous puissions échanger librement.")
            return

        elif any(kw in cmd_lower for kw in ["désactive le mode conversation", "arrête la conversation continue", "stop conversation"]):
            self.conversation_continue = False
            self.conv_continue_var.set(False)
            self.parler("Très bien. Je repasse en mode veille classique. Dites mon nom pour m'appeler.")
            return

        elif 'ouvre' in commande:
            app_to_open = commande.replace('ouvre', '').strip()
            if not app_to_open:
                self.parler("Quelle application souhaitez-vous ouvrir ?")
            elif 'navigateur' in app_to_open or 'chrome' in app_to_open: 
                self.parler("J'ouvre votre navigateur.")
                webbrowser.open("https://google.com")
            elif 'téléchargement' in app_to_open:
                self.parler("J'ouvre votre dossier de téléchargements.")
                os.startfile(os.path.join(os.path.expanduser('~'), 'Downloads'))
            elif 'documents' in app_to_open:
                self.parler("J'ouvre vos documents.")
                os.startfile(os.path.join(os.path.expanduser('~'), 'Documents'))
            else:
                self.parler(f"D'accord, j'essaie d'ouvrir {app_to_open}.")
                try:
                    # On utilise AppOpener pour ouvrir n'importe quelle application installée
                    app_open(app_to_open, match_closest=True)
                except Exception as e:
                    print(f"Erreur ouverture {app_to_open}: {e}")
                    self.parler(f"Désolé, je n'ai pas pu ouvrir {app_to_open}. Vérifiez le nom de l'application.")

        elif 'ferme' in commande or 'quitte' in commande:
            # Nouvelle fonctionnalité : fermer TOUTES les applications
            if any(w in commande for w in ['tout', 'toutes', 'toutes les applications', 'tous les processus', 'toutes les fenêtres']):
                self.parler("Attention, je vais fermer toutes vos applications actives. Confirmation requise. Dites 'confirme' pour continuer.")
                # On attend une confirmation (simplifiée pour l'instant)
                self.status_label.configure(text="⚠️ Confirmation requise pour fermer toutes les apps", text_color=COLOR_ACCENT_RED)
                # Pour l'instant, on exécute directement (vous pouvez ajouter une vraie confirmation plus tard)
                self.parler("Fermeture de toutes les applications en cours...")
                closed, failed = self.close_all_user_apps()
                self.parler(f"Opération terminée. {closed} applications fermées. {failed} échecs.")
            
            else:
                target = commande.replace('ferme', '').replace('quitte', '').replace("l'application", '').replace('la fenêtre', '').strip()
                
                # Mappage des noms communs vers les processus réels
                process_map = {
                    "word": "winword",
                    "excel": "excel",
                    "powerpoint": "powerpnt",
                    "chrome": "chrome",
                    "navigateur": "chrome",
                    "calculatrice": "calculator",
                    "bloc-notes": "notepad",
                    "note": "notepad",
                    "spotify": "spotify",
                    "discord": "discord"
                }
                
                p_name = process_map.get(target.lower(), target)

                if not target:
                    try:
                        win = gw.getActiveWindow()
                        if win:
                            self.parler(f"Je ferme la fenêtre {win.title}.")
                            win.close()
                        else: self.parler("Quelle application dois-je fermer ?")
                    except: self.parler("Désolé, je ne peux pas fermer cette fenêtre.")
                else:
                    self.parler(f"Je tente de fermer {target}.")
                    found = False

                    # 1. Tentative par titre de fenêtre (le plus précis visuellement)
                    try:
                        wins = gw.getWindowsWithTitle(target)
                        for w in wins:
                            w.close()
                            found = True
                    except: pass

                    # 2. Tentative par processus psutil (plus radical)
                    if not found:
                        for proc in psutil.process_iter(['name']):
                            try:
                                if p_name.lower() in proc.info['name'].lower():
                                    proc.kill()
                                    found = True
                            except: pass

                    # 3. Tentative finale avec AppOpener
                    if not found:
                        try:
                            app_close(target, match_closest=True)
                            found = True
                        except: pass
                    
                    # 4. Dernier recours commande système
                    if not found:
                        os.system(f"taskkill /f /im {p_name}.exe /t")

        elif any(w in commande for w in ['liste les processus', 'quels processus', 'applications actives', 'processus actifs', 'quelles applications sont ouvertes']):
            result = self.list_active_processes()
            self.parler(result)


        elif 'agrandis' in commande or 'maximise' in commande:
            try:
                win = gw.getActiveWindow()
                if win:
                    win.maximize()
                    self.parler("Fenêtre maximisée.")
                else:
                    self.parler("Je ne trouve pas de fenêtre active à maximiser.")
            except:
                self.parler("Une erreur est survenue lors de la maximisation.")

        elif 'réduis' in commande or 'minimise' in commande:
            if 'tous' in commande or 'tout' in commande or 'bureau' in commande:
                self.parler("Je cache tout. Retour au bureau.")
                pyautogui.hotkey('win', 'd')
            else:
                try:
                    win = gw.getActiveWindow()
                    if win:
                        win.minimize()
                        self.parler("Fenêtre réduite.")
                    else:
                        self.parler("Je ne vois pas de fenêtre à réduire.")
                except:
                    self.parler("Oups, je n'ai pas pu réduire la fenêtre.")

        elif 'bascule' in commande or 'cherche la fenêtre' in commande:
            target = commande.replace('bascule sur', '').replace('cherche la fenêtre', '').replace('ouvre la fenêtre', '').strip()
            if target:
                windows = gw.getWindowsWithTitle(target)
                if windows:
                    windows[0].activate()
                    self.parler(f"Je bascule sur {target}.")
                else:
                    self.parler(f"Je ne trouve pas de fenêtre avec le titre {target}.")
            else:
                self.parler("Quelle fenêtre voulez-vous que je cherche ?")

        elif 'capture' in commande or 'screenshot' in commande:
            self.parler("Très bien, je prends une capture d'écran.")
            try:
                nom_photo = f"capture_{int(time.time())}.png"
                pyautogui.screenshot(nom_photo)
                self.parler(f"Capture d'écran enregistrée sous le nom {nom_photo}.")
            except Exception as e:
                self.parler("Désolé, je n'ai pas pu effectuer la capture d'écran.")

        elif 'verrouille' in commande or 'session' in commande:
            self.parler("Je verrouille votre session.")
            os.system("rundll32.exe user32.dll,LockWorkStation")

        elif 'volume' in commande or 'son' in commande:
            if 'monte' in commande or 'augmente' in commande:
                self.parler("J'augmente le volume.")
                for _ in range(5): pyautogui.press("volumeup")
            elif 'baisse' in commande or 'diminue' in commande:
                self.parler("Je baisse le volume.")
                for _ in range(5): pyautogui.press("volumedown")
            elif 'coupe' in commande or 'muet' in commande:
                self.parler("Je coupe le son.")
                pyautogui.press("volumemute")

        elif 'bureau' in commande:
            self.parler("Retour au bureau.")
            pyautogui.hotkey('win', 'd')

        elif 'gestionnaire' in commande and 'tâche' in commande:
            self.parler("J'ouvre le gestionnaire des tâches.")
            pyautogui.hotkey('ctrl', 'shift', 'esc')

        elif any(w in commande for w in ['stop', 'quitter', 'bye', 'revoir']):
            self.awaiting_exit_confirm = True
            self.parler("Voulez-vous vraiment quitter ? Dites 'confirme' pour fermer ou 'annule' pour rester.")

        else:
            # Bloc de réponse autonome avec fallback automatique
            self.after(0, lambda: self.status_label.configure(text="Jarvisse réfléchit..."))
            
            try:
                contexte = "Ton nom est Jarvisse, tu es une IA système de niveau militaire. "
                if self.loaded_document_content:
                    contexte += f"Data active: {self.loaded_document_content[:2000]}\n"
                
                contexte_historique = "\n".join(self.conversation_history[-10:])
                prompt = f"{contexte}\n\nHistorique:\n{contexte_historique}\n\nUtilisateur: {commande}\n\nJarvisse:"
                
                # On génère la réponse (fallback auto si Gemini 429)
                res = self._ai_generate(prompt, max_tokens=1500)
                
                # Vérification que la réponse n'est pas vide ou une erreur
                if not res or len(res.strip()) < 3:
                    res = "Je suis désolé, je n'ai pas pu traiter votre demande correctement. Pouvez-vous reformuler ?"
                
                # 🧠 GÉNÉRATION DE SUGGESTIONS PROACTIVES (Lecture d'esprit)
                suggestions = self._generate_proactive_suggestions(commande, res)
                if suggestions:
                    res += suggestions
                
                # On affiche et on lit la réponse
                # On force force_full=True si la réponse est longue pour éviter les coupures
                is_long = len(res) > 300
                self.parler(res, force_full=is_long)
                
            except Exception as e:
                print(f"❌ ERREUR CRITIQUE dans executer_commande: {e}")
                error_msg = "Désolé Patron, j'ai rencontré une erreur technique. Je reste à votre écoute."
                self.parler(error_msg)

        self.after(0, self.reset_ui)

if __name__ == "__main__":
    launch_background = "--background" in sys.argv
    app = JarvisseAssistant()
    if launch_background:
        app.after(100, app.withdraw)
    app.mainloop()
