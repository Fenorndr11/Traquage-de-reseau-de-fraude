import tkinter as tk
from tkinter import ttk, messagebox
import math
import random
import time
from collections import deque

# PARTIE 1 — GÉNÉRATION DE G(n, p)
def generer_gnp(n, p):
    """
    Génère un graphe aléatoire G(n,p) selon le modèle d'Erdős–Rényi.
    Représentation : liste d'adjacence sous forme de dictionnaire
        { sommet : set(voisins) }
    """
    # Initialiser tous les sommets avec un ensemble vide de voisins
    G = {v: set() for v in range(n)}

    nb_aretes = 0
    for u in range(n):
        for v in range(u + 1, n):          # u < v → pas de boucle, pas de doublon
            if random.random() < p:        # Bernoulli(p)
                G[u].add(v)
                G[v].add(u)
                nb_aretes += 1

    return G, nb_aretes


def probabilite_gnp(n):
    """
    Calcule la probabilité p utilisée pour G(n,p).

    Formule : p = ln(n)/n + 0.1: seuil de connexité d'Erdős–Rényi, augmenté de 0.1 pour s'assurer que G est presque connexe avant connexification.

    Preuve du seuil :
        Soit X_v = 1 si le sommet v est isolé.
        E[X_v] = (1-p)^(n-1) ≈ e^{-p(n-1)}
        Si p = ln(n)/n : E[X_v] ≈ e^{-ln(n)} = 1/n
        E[nb isolés] = n · 1/n = 1  → fini, donc presque tous connectés
        Pour p > ln(n)/n, E[nb isolés] → 0  → connexe avec haute probabilité
    """
    if n <= 1:
        return 1.0
    p_seuil = math.log(n) / n
    return min(1.0, round(p_seuil + 0.1, 4))

# PARTIE 2 — TRANSFORMATION G → G' (connexe, simple, non orienté)

def bfs_composante(G, depart, visites):
    """
    BFS depuis 'depart', retourne l'ensemble des sommets atteignables
    Marque les sommets visités dans l'ensemble 'visites'.
    """
    composante = set()
    file = deque([depart])
    visites.add(depart)
    while file:
        v = file.popleft()
        composante.add(v)
        for voisin in G[v]:
            if voisin not in visites:
                visites.add(voisin)
                file.append(voisin)
    return composante


def trouver_composantes(G):
    """
    Trouve toutes les composantes connexes de G par BFS répété.
    Retourne une liste de sets de sommets.
    """
    visites = set()
    composantes = []
    for v in G:
        if v not in visites:
            comp = bfs_composante(G, v, visites)
            composantes.append(comp)
    return composantes


def connexifier(G):
    """
    Transforme G en G' : graphe simple, non orienté, connexe, sans boucle.
    """
    # Copie profonde du graphe (sets indépendants)
    Gp = {v: set(voisins) for v, voisins in G.items()}

    composantes = trouver_composantes(Gp)
    ponts_ajoutes = []

    if len(composantes) > 1:
        # Prendre un représentant de chaque composante
        representants = [min(comp) for comp in composantes]
        # Chaîner : rep[0]—rep[1]—rep[2]—...—rep[k-1]
        for i in range(len(representants) - 1):
            u = representants[i]
            v = representants[i + 1]
            Gp[u].add(v)
            Gp[v].add(u)
            ponts_ajoutes.append((u, v))

    return Gp, len(composantes), ponts_ajoutes

# PARTIE 3 — PARCOURS EN LARGEUR DE G' AVEC COLORIAGE


# Convention de couleurs BFS (algorithme CLRS) :
#   BLANC  : non découvert
#   GRIS   : découvert, en attente de traitement
#   NOIR   : traité (tous ses voisins explorés)

def bfs_colorie(Gp, source=0):
    """
    Parcours EN LARGEUR de G' depuis 'source'.
    Retourne :
      - ordre_visite : liste ordonnée des sommets visités
      - couleur      : dict { sommet → couleur finale }
      - distance     : dict { sommet → distance BFS depuis source }
      - parent       : dict { sommet → prédécesseur dans l'arbre BFS }
    """
    n = len(Gp)
    couleur  = {v: "BLANC" for v in Gp}
    distance = {v: -1     for v in Gp}
    parent   = {v: None   for v in Gp}
    ordre_visite = []

    couleur[source]  = "GRIS"
    distance[source] = 0
    file = deque([source])

    while file:
        u = file.popleft()
        ordre_visite.append(u)

        for v in sorted(Gp[u]):        
            if couleur[v] == "BLANC":
                couleur[v]  = "GRIS"
                distance[v] = distance[u] + 1
                parent[v]   = u
                file.append(v)

        couleur[u] = "NOIR"               

    return ordre_visite, couleur, distance, parent

# PARTIE 4 — ÉNUMÉRATION DES CLIQUES (Bron–Kerbosch avec pivot)
def bron_kerbosch(Gp, R, P, X, cliques):
    """
    Algorithme de Bron–Kerbosch avec pivot
    """
    if not P and not X:
        # R est une clique maximale
        if len(R) >= 2:                   # ignorer les sommets isolés
            cliques.append(frozenset(R))
        return

    pivot = max(P | X, key=lambda u: len(Gp[u] & P))

    for v in list(P - Gp[pivot]):
        bron_kerbosch(
            Gp,
            R | {v},
            P & Gp[v],
            X & Gp[v],
            cliques
        )
        P = P - {v}
        X = X | {v}


def enumerer_cliques(Gp):
    """Lance Bron–Kerbosch sur G' entier."""
    cliques = []
    P = set(Gp.keys())
    bron_kerbosch(Gp, set(), P, set(), cliques)
    # Trier par taille décroissante
    cliques.sort(key=len, reverse=True)
    return cliques

# PARTIE 5 — CLASSIFICATION DES SUSPECTS

def classifier_suspects(cliques, n, seuil_taille=3):
    """
    Classe les cliques en niveaux de suspicion.

    Critères :
      - CRITIQUE  : taille ≥ seuil_taille ET taille/n ≥ 0.15
      - ÉLEVÉ     : taille ≥ seuil_taille ET taille/n ≥ 0.08
      - MODÉRÉ    : taille ≥ seuil_taille
      - (ignorées): taille < seuil_taille

    Score = taille / n  (part du graphe que forme la clique)

    Dans le contexte de détection d'intrus :
      une grande clique = sous-réseau très dense où tous se connaissent
      → structure caractéristique d'un réseau organisé suspect
    """
    suspects = []
    for i, clique in enumerate(cliques):
        taille = len(clique)
        if taille < seuil_taille:
            continue

        score = round(taille / n, 4)

        if score >= 0.15:
            niveau = "CRITIQUE"
            couleur = "#ff4444"
        elif score >= 0.08:
            niveau = "ÉLEVÉ"
            couleur = "#ff9900"
        else:
            niveau = "MODÉRÉ"
            couleur = "#ffdd00"

        suspects.append({
            "id"      : i + 1,
            "clique"  : sorted(clique),
            "taille"  : taille,
            "score"   : score,
            "niveau"  : niveau,
            "couleur" : couleur,
        })

    return suspects

# PARTIE 6 — INTERFACE TKINTER

C = {
    "bg"      : "#0a0c12",
    "surface" : "#13161f",
    "surface2": "#1c2030",
    "border"  : "#2a3050",
    "accent"  : "#3d7fff",
    "text"    : "#dde3f5",
    "muted"   : "#5a6280",
    "green"   : "#3dba7f",
    "yellow"  : "#f0c040",
    "orange"  : "#f07030",
    "red"     : "#f03050",
    "white"   : "#ffffff",
}

MONO = ("Courier", 10)
MONO_B = ("Courier", 10, "bold")
MONO_S = ("Courier", 9)
MONO_T = ("Courier", 13, "bold")


class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("Analyse de graphe — Détection de cliques suspectes")
        self.geometry("1100x720")
        self.configure(bg=C["bg"])
        self.resizable(True, True)
        self._construire()

    #Construction 

    def _construire(self):
        # En-tête
        header = tk.Frame(self, bg=C["surface"], height=56)
        header.pack(fill="x")
        header.pack_propagate(False)
        tk.Label(header, text="◈  ANALYSE G(n,p) — CLIQUES SUSPECTES",
                 bg=C["surface"], fg=C["text"],
                 font=("Courier", 15, "bold"), padx=20).pack(side="left", pady=14)
        tk.Label(header, text="Erdős–Rényi  ·  Bron–Kerbosch  ·  BFS",
                 bg=C["surface"], fg=C["muted"],
                 font=MONO_S, padx=20).pack(side="right", pady=14)

        # Barre de saisie
        saisie = tk.Frame(self, bg=C["surface2"], height=52)
        saisie.pack(fill="x")
        saisie.pack_propagate(False)

        tk.Label(saisie, text="Taille n :", bg=C["surface2"], fg=C["muted"],
                 font=MONO).pack(side="left", padx=(20, 6), pady=14)

        self.var_n = tk.StringVar(value="20")
        champ_n = tk.Entry(saisie, textvariable=self.var_n, width=6,
                           bg=C["border"], fg=C["text"], insertbackground=C["text"],
                           font=MONO_B, relief="flat")
        champ_n.pack(side="left", ipady=5, pady=12)

        # Affichage de p calculé
        self.lbl_p = tk.Label(saisie, text="", bg=C["surface2"], fg=C["accent"],
                              font=MONO)
        self.lbl_p.pack(side="left", padx=16)
        self.var_n.trace_add("write", self._maj_p)
        self._maj_p()

        tk.Label(saisie, text="Seuil taille clique :", bg=C["surface2"],
                 fg=C["muted"], font=MONO).pack(side="left", padx=(30, 6))
        self.var_seuil = tk.StringVar(value="3")
        tk.Entry(saisie, textvariable=self.var_seuil, width=4,
                 bg=C["border"], fg=C["text"], insertbackground=C["text"],
                 font=MONO_B, relief="flat").pack(side="left", ipady=5, pady=12)

        btn = tk.Button(saisie, text="  ▶  GÉNÉRER & ANALYSER  ",
                        bg=C["accent"], fg=C["white"],
                        font=MONO_B, relief="flat", cursor="hand2",
                        activebackground="#2a5fcc", activeforeground=C["white"],
                        command=self._lancer)
        btn.pack(side="right", padx=20, pady=10, ipady=4)

        # Corps principal
        corps = tk.Frame(self, bg=C["bg"])
        corps.pack(fill="both", expand=True)

        # Colonne gauche : log + stats
        gauche = tk.Frame(corps, bg=C["bg"], width=360)
        gauche.pack(side="left", fill="y")
        gauche.pack_propagate(False)

        tk.Label(gauche, text="JOURNAL D'EXÉCUTION",
                 bg=C["bg"], fg=C["muted"], font=MONO_S, anchor="w"
                 ).pack(fill="x", padx=14, pady=(12, 4))

        self.log = tk.Text(gauche, bg=C["surface"], fg=C["text"],
                           font=MONO_S, relief="flat", state="disabled",
                           wrap="word", insertbackground=C["text"])
        sb_log = ttk.Scrollbar(gauche, orient="vertical", command=self.log.yview)
        self.log.configure(yscrollcommand=sb_log.set)
        self.log.pack(side="left", fill="both", expand=True, padx=(14, 0), pady=(0, 14))
        sb_log.pack(side="left", fill="y", pady=(0, 14))

        # Tags de couleur pour le log
        self.log.tag_configure("ok",    foreground=C["green"])
        self.log.tag_configure("info",  foreground=C["accent"])
        self.log.tag_configure("warn",  foreground=C["yellow"])
        self.log.tag_configure("head",  foreground=C["text"], font=("Courier", 10, "bold"))
        self.log.tag_configure("muted", foreground=C["muted"])

        # Séparateur
        tk.Frame(corps, bg=C["border"], width=1).pack(side="left", fill="y")

        # Colonne droite : résultats (notebook à onglets)
        droite = tk.Frame(corps, bg=C["bg"])
        droite.pack(side="left", fill="both", expand=True)

        style = ttk.Style()
        style.theme_use("clam")
        style.configure("TNotebook", background=C["bg"], borderwidth=0)
        style.configure("TNotebook.Tab",
                         background=C["surface2"], foreground=C["muted"],
                         font=MONO_S, padding=[12, 6])
        style.map("TNotebook.Tab",
                  background=[("selected", C["surface"])],
                  foreground=[("selected", C["text"])])

        self.notebook = ttk.Notebook(droite)
        self.notebook.pack(fill="both", expand=True, padx=10, pady=10)

        # Onglet 1 : Parcours BFS
        self.frame_bfs = tk.Frame(self.notebook, bg=C["surface"])
        self.notebook.add(self.frame_bfs, text="  Parcours BFS  ")

        # Onglet 2 : Cliques
        self.frame_cliques = tk.Frame(self.notebook, bg=C["surface"])
        self.notebook.add(self.frame_cliques, text="  Cliques  ")

        # Onglet 3 : Suspects
        self.frame_suspects = tk.Frame(self.notebook, bg=C["surface"])
        self.notebook.add(self.frame_suspects, text="  Suspects  ")

        # Pied de page
        footer = tk.Frame(self, bg=C["surface"], height=24)
        footer.pack(fill="x", side="bottom")
        footer.pack_propagate(False)
        self.lbl_footer = tk.Label(footer, text="En attente de génération…",
                                   bg=C["surface"], fg=C["muted"], font=MONO_S)
        self.lbl_footer.pack(side="left", padx=16, pady=4)

    def _maj_p(self, *_):
        """Met à jour l'affichage de p quand n change."""
        try:
            n = int(self.var_n.get())
            p = probabilite_gnp(n)
            seuil = round(math.log(n) / n, 4) if n > 1 else 1.0
            self.lbl_p.config(
                text=f"p = {p}  (seuil connexité = ln({n})/{n} ≈ {seuil})"
            )
        except (ValueError, ZeroDivisionError):
            self.lbl_p.config(text="")

    # ── Log ───────────────────────────────────────────────────

    def _log(self, texte, tag=""):
        self.log.config(state="normal")
        if tag:
            self.log.insert("end", texte + "\n", tag)
        else:
            self.log.insert("end", texte + "\n")
        self.log.see("end")
        self.log.config(state="disabled")

    def _log_clear(self):
        self.log.config(state="normal")
        self.log.delete("1.0", "end")
        self.log.config(state="disabled")

    # ── Lancement de l'analyse ────────────────────────────────

    def _lancer(self):
        # Validation des entrées
        try:
            n = int(self.var_n.get())
            if n < 3 or n > 150:
                raise ValueError
        except ValueError:
            messagebox.showerror("Erreur", "n doit être un entier entre 3 et 150")
            return
        try:
            seuil = int(self.var_seuil.get())
            if seuil < 2:
                raise ValueError
        except ValueError:
            messagebox.showerror("Erreur", "Le seuil de clique doit être ≥ 2")
            return

        self._log_clear()
        t0 = time.time()

        # ── Étape 1 : Génération G(n,p) ───────────────────────
        p = probabilite_gnp(n)
        esperance = round(n * (n - 1) / 2 * p, 1)
        self._log(f"━━ G(n,p) ━━━━━━━━━━━━━━━━━━━━━", "head")
        self._log(f"  n = {n}  |  p = {p}", "info")
        self._log(f"  E[|arêtes|] = C({n},2)·{p} = {esperance}", "muted")
        self._log(f"  seuil connexité ≈ ln({n})/{n} = {round(math.log(n)/n,4)}", "muted")

        G, nb_aretes_G = generer_gnp(n, p)
        self._log(f"  G généré : {n} sommets, {nb_aretes_G} arêtes réelles", "ok")

        # ── Étape 2 : G → G' ──────────────────────────────────
        self._log(f"\n━━ G → G' ━━━━━━━━━━━━━━━━━━━━━", "head")
        Gp, nb_comp, ponts = connexifier(G)
        nb_aretes_Gp = sum(len(v) for v in Gp.values()) // 2
        self._log(f"  Composantes dans G : {nb_comp}", "info")
        if ponts:
            self._log(f"  Ponts ajoutés     : {len(ponts)}", "warn")
            for u, v in ponts:
                self._log(f"    {u} ─── {v}", "muted")
        else:
            self._log(f"  G était déjà connexe ✓", "ok")
        self._log(f"  G' : {n} sommets, {nb_aretes_Gp} arêtes", "ok")
        self._log(f"  G' est simple, non orienté, connexe ✓", "ok")

        # ── Étape 3 : Parcours BFS ────────────────────────────
        self._log(f"\n━━ BFS depuis sommet 0 ━━━━━━━━━", "head")
        ordre, couleur, distance, parent = bfs_colorie(Gp, source=0)
        self._log(f"  Ordre de visite ({len(ordre)} sommets) :", "info")
        # Afficher par lignes de 10
        for i in range(0, len(ordre), 10):
            ligne = " → ".join(str(v) for v in ordre[i:i+10])
            self._log(f"    {ligne}", "muted")
        self._log(f"  Tous les sommets atteints ✓", "ok")

        # ── Étape 4 : Cliques ─────────────────────────────────
        self._log(f"\n━━ Bron–Kerbosch ━━━━━━━━━━━━━━━", "head")
        self._log(f"  Énumération des cliques maximales…", "info")
        cliques = enumerer_cliques(Gp)
        self._log(f"  {len(cliques)} cliques maximales trouvées", "ok")
        if cliques:
            self._log(f"  Plus grande clique : taille {len(cliques[0])}", "info")

        # ── Étape 5 : Suspects ────────────────────────────────
        self._log(f"\n━━ Classification ━━━━━━━━━━━━━━━", "head")
        suspects = classifier_suspects(cliques, n, seuil)
        self._log(f"  Seuil taille = {seuil}", "info")
        self._log(f"  {len(suspects)} cliques suspectes identifiées", "ok")
        for s in suspects[:5]:
            self._log(f"  [{s['niveau']:8s}] taille={s['taille']}  score={s['score']}", "warn")

        t1 = time.time()
        self._log(f"\n  Temps total : {round(t1-t0, 3)}s", "muted")

        # ── Mise à jour des onglets ───────────────────────────
        self._afficher_bfs(ordre, distance, n)
        self._afficher_cliques(cliques, n)
        self._afficher_suspects(suspects, n)

        self.lbl_footer.config(
            text=f"G({n},{p})  →  {nb_aretes_Gp} arêtes  |  "
                 f"{len(cliques)} cliques  |  {len(suspects)} suspects"
        )
        self.notebook.select(2 if suspects else 1)

    # ── Onglet BFS ────────────────────────────────────────────

    def _afficher_bfs(self, ordre, distance, n):
        for w in self.frame_bfs.winfo_children():
            w.destroy()

        tk.Label(self.frame_bfs, text="ORDRE DE VISITE BFS (colorié BLANC→GRIS→NOIR)",
                 bg=C["surface"], fg=C["muted"], font=MONO_S, anchor="w"
                 ).pack(fill="x", padx=14, pady=(10, 4))

        # Tableau des sommets avec leur distance BFS
        cols = ("sommet", "distance", "couleur_finale")
        style = ttk.Style()
        style.configure("BFS.Treeview",
                        background=C["surface"], foreground=C["text"],
                        fieldbackground=C["surface"], rowheight=26, font=MONO_S,
                        borderwidth=0)
        style.configure("BFS.Treeview.Heading",
                        background=C["surface2"], foreground=C["muted"],
                        font=MONO_S, relief="flat")
        style.map("BFS.Treeview",
                  background=[("selected", C["border"])],
                  foreground=[("selected", C["text"])])

        tree = ttk.Treeview(self.frame_bfs, columns=cols, show="headings",
                            style="BFS.Treeview")
        for col, txt, w in [("sommet","Sommet",80),("distance","Distance BFS",130),
                              ("couleur_finale","État final",120)]:
            tree.heading(col, text=txt)
            tree.column(col, width=w, anchor="center")

        tree.tag_configure("noir", foreground=C["muted"])
        tree.tag_configure("source", foreground=C["green"])

        for rang, v in enumerate(ordre):
            tag = "source" if rang == 0 else "noir"
            tree.insert("", "end", values=(v, distance[v], "■ NOIR"), tags=(tag,))

        sb = ttk.Scrollbar(self.frame_bfs, orient="vertical", command=tree.yview)
        tree.configure(yscrollcommand=sb.set)
        tree.pack(side="left", fill="both", expand=True, padx=(14, 0), pady=(0, 14))
        sb.pack(side="left", fill="y", pady=(0, 14))

    # ── Onglet Cliques ────────────────────────────────────────

    def _afficher_cliques(self, cliques, n):
        for w in self.frame_cliques.winfo_children():
            w.destroy()

        tk.Label(self.frame_cliques,
                 text=f"CLIQUES MAXIMALES ({len(cliques)} trouvées)",
                 bg=C["surface"], fg=C["muted"], font=MONO_S, anchor="w"
                 ).pack(fill="x", padx=14, pady=(10, 4))

        cols = ("rang", "taille", "sommets", "score")
        style = ttk.Style()
        style.configure("CLQ.Treeview",
                        background=C["surface"], foreground=C["text"],
                        fieldbackground=C["surface"], rowheight=28, font=MONO_S,
                        borderwidth=0)
        style.configure("CLQ.Treeview.Heading",
                        background=C["surface2"], foreground=C["muted"],
                        font=MONO_S, relief="flat")
        style.map("CLQ.Treeview",
                  background=[("selected", C["border"])],
                  foreground=[("selected", C["text"])])

        tree = ttk.Treeview(self.frame_cliques, columns=cols, show="headings",
                            style="CLQ.Treeview")
        for col, txt, w in [("rang","#",40), ("taille","Taille",70),
                              ("sommets","Sommets",380), ("score","Score",80)]:
            tree.heading(col, text=txt)
            tree.column(col, width=w, anchor="center" if col != "sommets" else "w")

        tree.tag_configure("grande", foreground=C["yellow"])
        tree.tag_configure("moy",    foreground=C["text"])
        tree.tag_configure("petite", foreground=C["muted"])

        for i, clique in enumerate(cliques):
            taille = len(clique)
            score  = round(taille / n, 3)
            sommets_str = "{" + ", ".join(str(v) for v in sorted(clique)) + "}"
            tag = "grande" if taille >= 4 else ("moy" if taille == 3 else "petite")
            tree.insert("", "end",
                        values=(i+1, taille, sommets_str, score),
                        tags=(tag,))

        sb = ttk.Scrollbar(self.frame_cliques, orient="vertical", command=tree.yview)
        tree.configure(yscrollcommand=sb.set)
        tree.pack(side="left", fill="both", expand=True, padx=(14, 0), pady=(0, 14))
        sb.pack(side="left", fill="y", pady=(0, 14))

    # ── Onglet Suspects ───────────────────────────────────────

    def _afficher_suspects(self, suspects, n):
        for w in self.frame_suspects.winfo_children():
            w.destroy()

        if not suspects:
            tk.Label(self.frame_suspects,
                     text="Aucune clique suspecte détectée\n(augmente n ou diminue le seuil)",
                     bg=C["surface"], fg=C["muted"],
                     font=("Courier", 12), justify="center"
                     ).place(relx=0.5, rely=0.5, anchor="center")
            return

        # En-tête résumé
        hdr = tk.Frame(self.frame_suspects, bg=C["surface2"])
        hdr.pack(fill="x", padx=14, pady=(10, 0))

        for niveau, couleur, compte in [
            ("CRITIQUE", C["red"],    sum(1 for s in suspects if s["niveau"]=="CRITIQUE")),
            ("ÉLEVÉ",    C["orange"], sum(1 for s in suspects if s["niveau"]=="ÉLEVÉ")),
            ("MODÉRÉ",   C["yellow"], sum(1 for s in suspects if s["niveau"]=="MODÉRÉ")),
        ]:
            tk.Label(hdr, text=f"  {niveau}: {compte}  ",
                     bg=C["surface2"], fg=couleur,
                     font=MONO_B, padx=10, pady=6
                     ).pack(side="left", padx=4, pady=6)

        tk.Label(self.frame_suspects,
                 text=f"CLIQUES SUSPECTES ({len(suspects)} identifiées — sous-réseaux denses)",
                 bg=C["surface"], fg=C["muted"], font=MONO_S, anchor="w"
                 ).pack(fill="x", padx=14, pady=(8, 4))

        # Tableau
        cols = ("id", "niveau", "taille", "score", "membres")
        style = ttk.Style()
        style.configure("SUS.Treeview",
                        background=C["surface"], foreground=C["text"],
                        fieldbackground=C["surface"], rowheight=30, font=MONO_S,
                        borderwidth=0)
        style.configure("SUS.Treeview.Heading",
                        background=C["surface2"], foreground=C["muted"],
                        font=MONO_S, relief="flat")
        style.map("SUS.Treeview",
                  background=[("selected", C["border"])],
                  foreground=[("selected", C["text"])])

        tree = ttk.Treeview(self.frame_suspects, columns=cols, show="headings",
                            style="SUS.Treeview")
        for col, txt, w in [("id","#",40), ("niveau","Niveau",90),
                              ("taille","Taille",70), ("score","Score",80),
                              ("membres","Membres (sommets)",320)]:
            tree.heading(col, text=txt)
            tree.column(col, width=w, anchor="center" if col != "membres" else "w")

        tree.tag_configure("CRITIQUE", foreground=C["red"])
        tree.tag_configure("ÉLEVÉ",    foreground=C["orange"])
        tree.tag_configure("MODÉRÉ",   foreground=C["yellow"])

        for s in suspects:
            membres_str = "{" + ", ".join(str(v) for v in s["clique"]) + "}"
            tree.insert("", "end",
                        values=(s["id"], s["niveau"], s["taille"],
                                s["score"], membres_str),
                        tags=(s["niveau"],))

        sb = ttk.Scrollbar(self.frame_suspects, orient="vertical", command=tree.yview)
        tree.configure(yscrollcommand=sb.set)
        tree.pack(side="left", fill="both", expand=True, padx=(14, 0), pady=(0, 14))
        sb.pack(side="left", fill="y", pady=(0, 14))


# MAIN

if __name__ == "__main__":
    random.seed()          # seed aléatoire réel (pas fixé)
    app = App()
    app.mainloop()
