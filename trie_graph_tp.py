# TP2 - Trie e Grafo
# Estruturas de Dados e Algoritmos Avancados

from collections import deque
import heapq
import sys


class TrieNode:
    def __init__(self):
        self.children = {}
        self.is_end = False


class Trie:
    def __init__(self):
        self.root = TrieNode()

    def insert(self, word):
        no = self.root
        for letra in word:
            if letra not in no.children:
                no.children[letra] = TrieNode()
            no = no.children[letra]
        no.is_end = True

    def _achar_no(self, texto):
        no = self.root
        for letra in texto:
            if letra not in no.children:
                return None
            no = no.children[letra]
        return no

    def search(self, word):
        # so retorna True se for palavra completa (is_end = True)
        # palavra vazia nao e suportada
        if word == "":
            return False
        no = self._achar_no(word)
        if no is None:
            return False
        return no.is_end

    def starts_with(self, prefix):
        if prefix == "":
            return True
        no = self._achar_no(prefix)
        return no is not None

    def _collect_words(self, no, prefixo):
        palavras = []
        if no.is_end:
            palavras.append(prefixo)
        for letra in no.children:
            filho = no.children[letra]
            palavras = palavras + self._collect_words(filho, prefixo + letra)
        return palavras

    def autocomplete(self, prefix, k):
        no = self._achar_no(prefix)
        if no is None:
            return []
        palavras = self._collect_words(no, prefix)
        palavras.sort()
        return palavras[:k]

    def autocorrect(self, word):
        if self.search(word):
            return word

        todas = self._collect_words(self.root, "")
        melhor = None
        maior_prefixo = -1

        for candidata in todas:
            tamanho = 0
            for i in range(min(len(word), len(candidata))):
                if word[i] != candidata[i]:
                    break
                tamanho += 1

            if tamanho > maior_prefixo:
                maior_prefixo = tamanho
                melhor = candidata
            elif tamanho == maior_prefixo and candidata < melhor:
                melhor = candidata

        return melhor


# --- GRAFO LISTA ---

class GraphAdjList:
    def __init__(self, directed=False):
        self.adj = {}
        self.directed = directed

    def add_vertex(self, v):
        if v not in self.adj:
            self.adj[v] = []

    def add_edge(self, u, v, directed=None):
        if directed is None:
            directed = self.directed
        self.add_vertex(u)
        self.add_vertex(v)
        if v not in self.adj[u]:
            self.adj[u].append(v)
        if not directed:
            if u not in self.adj[v]:
                self.adj[v].append(u)

    def has_edge(self, u, v):
        if u not in self.adj:
            return False
        return v in self.adj[u]

    def neighbors_sorted(self, v):
        return sorted(self.adj.get(v, []))

    def dfs(self, start, sort_neighbors=True):
        visitados = []
        marcados = set()

        def _dfs(v):
            marcados.add(v)
            visitados.append(v)
            vizinhos = self.neighbors_sorted(v) if sort_neighbors else self.adj.get(v, [])
            for w in vizinhos:
                if w not in marcados:
                    _dfs(w)

        _dfs(start)
        return visitados

    def bfs(self, start, sort_neighbors=True):
        visitados = []
        marcados = {start}
        fila = deque([start])

        while fila:
            v = fila.popleft()
            visitados.append(v)
            vizinhos = self.neighbors_sorted(v) if sort_neighbors else self.adj.get(v, [])
            for w in vizinhos:
                if w not in marcados:
                    marcados.add(w)
                    fila.append(w)

        return visitados

    def componentes_conectadas(self):
        marcados = set()
        count = 0
        for v in self.adj:
            if v not in marcados:
                count += 1
                fila = deque([v])
                marcados.add(v)
                while fila:
                    u = fila.popleft()
                    for w in self.adj[u]:
                        if w not in marcados:
                            marcados.add(w)
                            fila.append(w)
        return count

    def conectado(self, origem, destino):
        if origem not in self.adj or destino not in self.adj:
            return False
        marcados = {origem}
        fila = deque([origem])
        while fila:
            v = fila.popleft()
            if v == destino:
                return True
            for w in self.adj[v]:
                if w not in marcados:
                    marcados.add(w)
                    fila.append(w)
        return False

    def menor_caminho_nao_ponderado(self, origem, destino):
        if origem not in self.adj or destino not in self.adj:
            return None, -1
        if origem == destino:
            return [origem], 0

        marcados = {origem}
        fila = deque([(origem, [origem])])

        while fila:
            v, caminho = fila.popleft()
            for w in self.adj[v]:
                if w in marcados:
                    continue
                novo = caminho + [w]
                if w == destino:
                    return novo, len(novo) - 1
                marcados.add(w)
                fila.append((w, novo))

        return None, -1

    def to_mermaid(self, directed=False):
        linhas = ["graph TD"]
        ja_imprimiu = []

        for u in self.adj:
            for v in self.adj[u]:
                if directed:
                    linhas.append("    " + str(u) + " --> " + str(v))
                else:
                    par = tuple(sorted([str(u), str(v)]))
                    if par in ja_imprimiu:
                        continue
                    ja_imprimiu.append(par)
                    linhas.append("    " + str(u) + " --- " + str(v))

        return "\n".join(linhas)


# --- GRAFO MATRIZ ---

class GraphAdjMatrix:
    def __init__(self):
        self.index = {}
        self.mat = []

    def add_vertex(self, v):
        if v in self.index:
            return
        i = len(self.mat)
        self.index[v] = i
        for linha in self.mat:
            linha.append(0)
        self.mat.append([0] * (i + 1))

    def add_edge(self, u, v, directed=False):
        self.add_vertex(u)
        self.add_vertex(v)
        i = self.index[u]
        j = self.index[v]
        self.mat[i][j] = 1
        if not directed:
            self.mat[j][i] = 1

    def has_edge(self, u, v):
        if u not in self.index or v not in self.index:
            return False
        i = self.index[u]
        j = self.index[v]
        return self.mat[i][j] == 1


# --- funcao do exercicio 11 ---

def find_vertices_by_prefix(trie, grafo, prefixo, k):
    candidatos = trie.autocomplete(prefixo, k=100)
    resultado = []
    for nome in candidatos:
        if nome in grafo.adj:
            resultado.append(nome)
        if len(resultado) == k:
            break
    return resultado


def montar_grafo_teste():
    g = GraphAdjList()
    vertices = ["A", "B", "C", "D", "E", "F", "G", "H", "I", "J"]
    for v in vertices:
        g.add_vertex(v)

    arestas = [
        ("A", "B"), ("A", "C"), ("B", "D"), ("B", "E"),
        ("C", "F"), ("D", "G"), ("E", "G"), ("F", "H"),
        ("G", "I"), ("H", "I"), ("I", "J"), ("E", "F"),
    ]
    for u, v in arestas:
        g.add_edge(u, v)

    return g


def montar_grafo_matriz():
    g = GraphAdjMatrix()
    arestas = [
        ("A", "B"), ("A", "C"), ("B", "D"), ("B", "E"),
        ("C", "F"), ("D", "G"), ("E", "G"), ("F", "H"),
        ("G", "I"), ("H", "I"), ("I", "J"), ("E", "F"),
    ]
    for u, v in arestas:
        g.add_edge(u, v)
    return g


# --- GRAFO PONDERADO ---

class WeightedGraph:
    def __init__(self):
        self.adj = {}

    def add_vertex(self, v):
        if v not in self.adj:
            self.adj[v] = []

    def add_edge(self, u, v, peso):
        self.add_vertex(u)
        self.add_vertex(v)
        self.adj[u].append((v, peso))
        self.adj[v].append((u, peso))

    def alcancaveis_bfs(self, origem):
        if origem not in self.adj:
            return []
        marcados = {origem}
        fila = deque([origem])
        ordem = [origem]
        while fila:
            v = fila.popleft()
            for w, _ in self.adj[v]:
                if w not in marcados:
                    marcados.add(w)
                    fila.append(w)
                    ordem.append(w)
        return ordem

    def menor_caminho_arestas(self, origem, destino):
        g = GraphAdjList()
        for u in self.adj:
            g.add_vertex(u)
            for v, _ in self.adj[u]:
                g.add_edge(u, v)
        return g.menor_caminho_nao_ponderado(origem, destino)

    def custo_caminho(self, caminho):
        total = 0
        for i in range(len(caminho) - 1):
            u, v = caminho[i], caminho[i + 1]
            for viz, peso in self.adj[u]:
                if viz == v:
                    total += peso
                    break
        return total

    def dijkstra(self, origem):
        dist = {v: float("inf") for v in self.adj}
        pred = {v: None for v in self.adj}
        dist[origem] = 0
        heap = [(0, origem)]
        visitados = set()

        while heap:
            d, u = heapq.heappop(heap)
            if u in visitados:
                continue
            visitados.add(u)
            for v, peso in self.adj[u]:
                nd = d + peso
                if nd < dist[v]:
                    dist[v] = nd
                    pred[v] = u
                    heapq.heappush(heap, (nd, v))

        return dist, pred

    def reconstruir_caminho(self, pred, destino):
        if pred.get(destino) is None and destino not in pred:
            return []
        caminho = []
        v = destino
        while v is not None:
            caminho.append(v)
            v = pred[v]
        caminho.reverse()
        return caminho


# --- EXERCICIOS 1-12 ---

def contar_times(n, amizades):
    g = GraphAdjList()
    for i in range(1, n + 1):
        g.add_vertex(i)
    for a, b in amizades:
        g.add_edge(a, b)
    return g.componentes_conectadas()


def contar_passeios_validos(s, tuneis, passeios):
    g = GraphAdjList()
    for i in range(1, s + 1):
        g.add_vertex(i)
    for x, y in tuneis:
        g.add_edge(x, y)

    validos = 0
    for seq in passeios:
        ok = True
        for i in range(len(seq) - 1):
            if not g.conectado(seq[i], seq[i + 1]):
                ok = False
                break
        if ok:
            validos += 1
    return validos


def processar_conectividade_dinamica(n, operacoes):
    g = GraphAdjList()
    for i in range(1, n + 1):
        g.add_vertex(i)
    respostas = []
    for tipo, a, b in operacoes:
        if tipo == 1:
            g.add_edge(a, b)
        else:
            respostas.append(1 if g.conectado(a, b) else 0)
    return respostas


def montar_grafo_produtos():
    g = GraphAdjList()
    arestas = [
        ("brush", "nail_polish"),
        ("nail_polish", "eye_shadow"),
        ("eye_shadow", "eye_glasses"),
        ("nail_polish", "nails"),
        ("nails", "pins"),
        ("nails", "needles"),
        ("pins", "needles"),
        ("nails", "hammer"),
        ("hammer", "drill"),
        ("hammer", "saw"),
        ("saw", "knife"),
        ("knife", "fork"),
        ("knife", "spoon"),
    ]
    for u, v in arestas:
        g.add_edge(u, v)
    return g


def montar_rede_social():
    g = GraphAdjList()
    arestas = [
        ("Idris", "Kamil"),
        ("Idris", "Talia"),
        ("Kamil", "Lina"),
        ("Lina", "Sasha"),
        ("Sasha", "Marco"),
        ("Marco", "Ken"),
        ("Ken", "Talia"),
    ]
    for u, v in arestas:
        g.add_edge(u, v)
    return g


def montar_grafo_dependencias():
    g = GraphAdjList(directed=True)
    arestas = [
        ("Inicio", "A"),
        ("Inicio", "B"),
        ("A", "C"),
        ("B", "C"),
        ("C", "D"),
        ("D", "E"),
        ("B", "F"),
        ("F", "E"),
    ]
    for u, v in arestas:
        g.add_edge(u, v)
    return g


def montar_rede_logistica():
    g = WeightedGraph()
    arestas = [
        ("Berco_A", "Patio_1", 4),
        ("Berco_A", "Patio_2", 7),
        ("Berco_B", "Patio_2", 3),
        ("Berco_B", "Patio_3", 6),
        ("Patio_1", "Patio_2", 2),
        ("Patio_2", "Patio_3", 2),
        ("Patio_1", "Alfandega", 8),
        ("Patio_2", "Alfandega", 5),
        ("Patio_3", "Centro_Logistico", 4),
        ("Alfandega", "Centro_Logistico", 3),
    ]
    for u, v, w in arestas:
        g.add_edge(u, v, w)
    return g


def dfs_ponderado(g_peso, start):
    g = GraphAdjList()
    for u in g_peso.adj:
        g.add_vertex(u)
        for v, _ in g_peso.adj[u]:
            g.add_edge(u, v)
    return g.dfs(start)


def bfs_ponderado(g_peso, start):
    g = GraphAdjList()
    for u in g_peso.adj:
        g.add_vertex(u)
        for v, _ in g_peso.adj[u]:
            g.add_edge(u, v)
    return g.bfs(start)


# --- ENTRADA STDIN (exercicios 1-3) ---

def ler_exercicio_1():
    linha = sys.stdin.readline().split()
    n, m = int(linha[0]), int(linha[1])
    amizades = []
    for _ in range(m):
        i, j = map(int, sys.stdin.readline().split())
        amizades.append((i, j))
    print(contar_times(n, amizades))


def ler_exercicio_2():
    linha = sys.stdin.readline().split()
    s, t = int(linha[0]), int(linha[1])
    tuneis = []
    for _ in range(t):
        x, y = map(int, sys.stdin.readline().split())
        tuneis.append((x, y))
    p = int(sys.stdin.readline())
    passeios = []
    for _ in range(p):
        dados = list(map(int, sys.stdin.readline().split()))
        passeios.append(dados[1:])
    print(contar_passeios_validos(s, tuneis, passeios))


def ler_exercicio_3():
    linha = sys.stdin.readline().split()
    n, m = int(linha[0]), int(linha[1])
    operacoes = []
    for _ in range(m):
        tipo, a, b = map(int, sys.stdin.readline().split())
        operacoes.append((tipo, a, b))
    for r in processar_conectividade_dinamica(n, operacoes):
        print(r)


# --- DEMONSTRACOES (exercicios 4-12) ---

def demo_exercicio_1():
    print("=" * 60)
    print("EXERCICIO 1 - Formacao de times")
    print("=" * 60)
    n, amizades = 6, [(1, 2), (2, 3), (4, 5)]
    print(f"Alunos: {n}, Amizades: {amizades}")
    print(f"Times formados: {contar_times(n, amizades)}")
    print("Complexidade: O(N + M) com BFS/DFS para componentes conectadas.")


def demo_exercicio_2():
    print("\n" + "=" * 60)
    print("EXERCICIO 2 - Validacao de passeios")
    print("=" * 60)
    tuneis = [(1, 2), (2, 3), (4, 5)]
    passeios = [[1, 2, 3], [1, 4], [3, 5]]
    print(f"Passeios validos: {contar_passeios_validos(5, tuneis, passeios)}")
    print("Complexidade: O(S + T + P * L * (S + T)), L = tamanho medio das sequencias.")


def demo_exercicio_3():
    print("\n" + "=" * 60)
    print("EXERCICIO 3 - Conectividade dinamica")
    print("=" * 60)
    ops = [(1, 1, 2), (0, 1, 3), (1, 2, 3), (0, 1, 3)]
    print(f"Respostas: {processar_conectividade_dinamica(3, ops)}")
    print("Complexidade: O(M * (N + arestas)) por consulta com BFS/DFS.")


def demo_exercicio_4():
    print("\n" + "=" * 60)
    print("EXERCICIO 4 - DFS em recomendacoes")
    print("=" * 60)
    g = montar_grafo_produtos()
    print(f"Ordem DFS a partir de 'nails': {g.dfs('nails')}")
    print("Complexidade: O(V + E).")


def demo_exercicio_5():
    print("\n" + "=" * 60)
    print("EXERCICIO 5 - BFS em recomendacoes")
    print("=" * 60)
    g = montar_grafo_produtos()
    ordem_bfs = g.bfs("nails")
    ordem_dfs = g.dfs("nails")
    print(f"Ordem BFS a partir de 'nails': {ordem_bfs}")
    print(f"Comparacao com DFS ({ordem_dfs}):")
    print("  DFS aprofunda caminhos antes de retornar; BFS visita por camadas.")


def demo_exercicio_6():
    print("\n" + "=" * 60)
    print("EXERCICIO 6 - Menor caminho em rede social")
    print("=" * 60)
    g = montar_rede_social()
    caminho, dist = g.menor_caminho_nao_ponderado("Idris", "Lina")
    print(f"Caminho minimo Idris -> Lina: {' -> '.join(caminho)}")
    print(f"Distancia (arestas): {dist}")


def demo_exercicio_7():
    print("\n" + "=" * 60)
    print("EXERCICIO 7 - Travessia em grafo direcionado")
    print("=" * 60)
    g = montar_grafo_dependencias()
    print(f"Ordem DFS: {g.dfs('Inicio')}")
    print(f"Ordem BFS: {g.bfs('Inicio')}")


def demo_exercicio_8():
    print("\n" + "=" * 60)
    print("EXERCICIO 8 - Viabilidade operacional")
    print("=" * 60)
    g = montar_rede_logistica()
    origem, destino = "Berco_A", "Centro_Logistico"
    caminho, etapas = g.menor_caminho_arestas(origem, destino)
    print(f"Areas alcancaveis: {g.alcancaveis_bfs(origem)}")
    print(f"Menor caminho em etapas: {' -> '.join(caminho)} ({etapas} arestas)")
    print(f"Custo total: {g.custo_caminho(caminho)}")


def demo_exercicio_9():
    print("\n" + "=" * 60)
    print("EXERCICIO 9 - Menor custo com Dijkstra")
    print("=" * 60)
    g = montar_rede_logistica()
    dist, _ = g.dijkstra("Berco_A")
    for v in sorted(dist.keys()):
        if v != "Berco_A":
            print(f"  Berco_A -> {v}: {dist[v]}")


def demo_exercicio_10():
    print("\n" + "=" * 60)
    print("EXERCICIO 10 - Reconstrucao de rota otima")
    print("=" * 60)
    g = montar_rede_logistica()
    _, pred = g.dijkstra("Berco_A")
    caminho = g.reconstruir_caminho(pred, "Centro_Logistico")
    print(f"Caminho minimo: {' -> '.join(caminho)}")


def demo_exercicio_11():
    print("\n" + "=" * 60)
    print("EXERCICIO 11 - Impacto dos pesos na escolha de rotas")
    print("=" * 60)
    g = montar_rede_logistica()
    origem, destino = "Berco_A", "Centro_Logistico"
    caminho_bfs, _ = g.menor_caminho_arestas(origem, destino)
    _, pred = g.dijkstra(origem)
    caminho_dijk = g.reconstruir_caminho(pred, destino)
    print(f"Caminho BFS:      {' -> '.join(caminho_bfs)}  (custo: {g.custo_caminho(caminho_bfs)})")
    print(f"Caminho Dijkstra: {' -> '.join(caminho_dijk)}  (custo: {g.custo_caminho(caminho_dijk)})")


def demo_exercicio_12():
    print("\n" + "=" * 60)
    print("EXERCICIO 12 - Analise de rotas na rede logistica")
    print("=" * 60)
    g = montar_rede_logistica()
    origem = "Berco_A"
    print(f"Ordem DFS: {dfs_ponderado(g, origem)}")
    print(f"Ordem BFS: {bfs_ponderado(g, origem)}")
    dist, _ = g.dijkstra(origem)
    print("Distancias minimas (Dijkstra):")
    for v in sorted(dist.keys()):
        print(f"  {origem} -> {v}: {dist[v]}")
