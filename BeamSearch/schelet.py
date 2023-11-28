import random, math
from _functools import reduce
from copy import copy, deepcopy
from builtins import isinstance
from resource import setrlimit, RLIMIT_AS, RLIMIT_DATA
from heapq import heappop, heappush, nsmallest, heapify
from math import sqrt
import sys, threading, resource
import faulthandler
import time


class NPuzzle:
	"""
	Reprezentarea unei stări a problemei și a istoriei mutărilor care au adus starea aici.
	
	Conține funcționalitate pentru
	- afișare
	- citirea unei stări dintr-o intrare pe o linie de text
	- obținerea sau ștergerea istoriei de mutări
	- obținerea variantei rezolvate a acestei probleme
	- verificarea dacă o listă de mutări fac ca această stare să devină rezolvată.
	"""

	NMOVES = 4
	UP, DOWN, LEFT, RIGHT = range(NMOVES)
	ACTIONS = [UP, DOWN, LEFT, RIGHT]
	names = "UP, DOWN, LEFT, RIGHT".split(", ")
	BLANK = ' '
	delta = dict(zip(ACTIONS, [(-1, 0), (1, 0), (0, -1), (0, 1)]))
	
	PAD = 2
	
	def __init__(self, puzzle : list[int | str], movesList : list[int] = []):
		"""
		Creează o stare nouă pe baza unei liste liniare de piese, care se copiază.
		
		Opțional, se poate copia și lista de mutări dată.
		"""
		self.N = len(puzzle)
		self.side = int(math.sqrt(self.N))
		self.r = copy(puzzle)
		self.moves = copy(movesList)
	
	def display(self, show = True) -> str:
		l = "-" * ((NPuzzle.PAD + 1) * self.side + 1)
		aslist = self.r
		
		slices = [aslist[ slice * self.side : (slice+1) * self.side ]  for slice in range(self.side)]
		s = ' |\n| '.join([' '.join([str(e).rjust(NPuzzle.PAD, ' ') for e in line]) for line in slices]) 
	
		s = ' ' + l + '\n| ' + s + ' |\n ' + l
		if show: print(s)
		return s
	def display_moves(self):
		print([self.names[a] if a is not None else None for a in self.moves])
		
	def print_line(self):
		return str(self.r)
	
	@staticmethod
	def read_from_line(line : str):
		list = line.strip('\n][').split(', ')
		numeric = [NPuzzle.BLANK if e == "' '" else int(e) for e in list]
		return NPuzzle(numeric)
	
	def clear_moves(self):
		"""Șterge istoria mutărilor pentru această stare."""
		self.moves.clear()
	
	def apply_move_inplace(self, move : int):
		"""Aplică o mutare, modificând această stare."""
		blankpos = self.r.index(NPuzzle.BLANK)
		y, x = blankpos // self.side, blankpos % self.side
		ny, nx = y + NPuzzle.delta[move][0], x + NPuzzle.delta[move][1]
		if ny < 0 or ny >= self.side or nx < 0 or nx >= self.side: return None
		newpos = ny * self.side + nx
		piece = self.r[newpos]
		self.r[blankpos] = piece
		self.r[newpos] = NPuzzle.BLANK
		self.moves.append(move)
		return self
	
	def get_allowed_moves(self):
		succ = []
		for action in self.ACTIONS:
				move = self.apply_move(action)
				if move is not None:
					succ.append(move)
		return succ
	
	def apply_move(self, move : int):
		"""Construiește o nouă stare, rezultată în urma aplicării mutării date."""
		return self.clone().apply_move_inplace(move)

	def solved(self):
		"""Întoarce varianta rezolvată a unei probleme de aceeași dimensiune."""
		return NPuzzle(list(range(self.N))[1:] + [NPuzzle.BLANK])

	def verify_solved(self, moves : list[int]) -> bool:
		""""Verifică dacă aplicarea mutărilor date pe starea curentă duce la soluție"""
		return reduce(lambda s, m: s.apply_move_inplace(m), moves, self.clone()) == self.solved()

	def clone(self):
		return NPuzzle(self.r, self.moves)
	def __str__(self) -> str:
		return str(self.N-1) + "-puzzle:" + str(self.r)
	def __repr__(self) -> str: return str(self)
	def __eq__(self, other):
		return self.r == other.r
	def __lt__(self, other):
		return True
	def __hash__(self):
		return hash(tuple(self.r))

def manhattan_heuristic(state):
		sum = 0
		for i in range(state.N):
			curr_x, curr_y = divmod(i, state.side)
			if state.r[i] != ' ':
				sum+= abs(good_pos[state.r[i]][0] - curr_x) + abs(good_pos[state.r[i]][1] - curr_y)
		return sum

def manhattan_linear_conflicts_heuristic(state):
	conflicts = 0
	for i in range(state.side):
		for left in range(state.side):
			for right in range(left + 1, state.side):
				# row
				pos_left = i * state.side + left
				pos_right = i * state.side + right
				if state.r[pos_left] != ' ' and state.r[pos_right] != ' ':
					lefty, leftx = good_pos[state.r[pos_left]]
					righty, rightx = good_pos[state.r[pos_right]]
					if lefty == i and righty == i and leftx > rightx:
						conflicts += 1
				# column
				pos_left = left * state.side + i
				pos_right = right * state.side + i
				if state.r[pos_left] != ' ' and state.r[pos_right] != ' ':
					lefty, leftx = good_pos[state.r[pos_left]]
					righty, rightx = good_pos[state.r[pos_right]]
					if leftx == i and rightx == i and lefty > righty:
						conflicts += 1

	return manhattan_heuristic(state) + 2 * conflicts

def euclidean_heuristic(state):
	sum = 0
	for i in range(state.N):
			curr_x, curr_y = divmod(i, state.side)
			if state.r[i] != ' ':
				sum+= sqrt((good_pos[state.r[i]][0] - curr_x)**2 + (good_pos[state.r[i]][1] - curr_y)**2)
	return sum

def count_not_placed(state):
	sum = 0
	for i in range(state.N):
				if state.r[i] != ' ' and i != state.r[i] - 1:
					sum+= 1
	return sum


def astar(start, h):
	frontier = []
	heappush(frontier, (0 + h(start), start))
	discovered = {start: (None, 0)}
	while frontier:
		_, curr = heappop(frontier)
		_, cost = discovered[curr]
		if curr == curr.solved():
			return curr, len(discovered)

		for move in curr.get_allowed_moves():
			if move not in discovered or cost + 1 < discovered[move][1]:
				discovered[move] = (curr, cost + 1)
				heappush(frontier, (discovered[move][1] + h(move), move))
	
	return None


def beam_search(start ,B, h, limita):
	beam = []
	heappush(beam, (h(start), start))
	vizitat = set()
	vizitat.add(start)
	while beam and len(vizitat) < limita:
		succ = []
		for s in beam:
			for move in s[1].get_allowed_moves():
				if move not in vizitat:
					heappush(succ, (h(move), move))
		for s in succ:
			if s[1].solved() == s[1]:
				print(len(s[1].moves), len(vizitat),sep=",")
				return 'SUCCES'
		selectat = nsmallest(B, succ)
		heapify(selectat)
		for _, s in selectat:
			vizitat.add(s)
		beam = selectat.copy()
	return "FAIL"

def glds(start, h, limita):
	vizitat = set()
	vizitat.add(start)
	discrepante = 0
	while True:
		if iteratie_glds(start, discrepante, h, vizitat, limita) == "SUCCES":
			return "SUCCES"
		discrepante += 1

def iteratie_glds(stare, discrepante, h, vizitat, limita):
	succ = []
	for move in stare.get_allowed_moves():
		if move is not None:
			if move == move.solved():
				print(len(move.moves), len(vizitat), sep=",")
				return "SUCCES"
			if move not in vizitat:
				heappush(succ, (h(move), move))
	if not succ:
		return "FAIL"
	if len(vizitat) > limita:
		return "FAIL"
	
	_, best = heappop(succ)
	
	if discrepante == 0:
		vizitat.add(best)
		res = iteratie_glds(best, 0, h, vizitat, limita)
		vizitat.remove(best)
		return res
	else:
		while succ:
			_, best_s = heappop(succ)
			vizitat.add(best_s)
			res = iteratie_glds(best_s, discrepante - 1, h, vizitat, limita)
			vizitat.remove(best_s)
			if res == "SUCCES":
				return "SUCCES"
		vizitat.add(best)
		res = iteratie_glds(best, discrepante, h, vizitat, limita)
		vizitat.remove(best)
		return res

def blds(start, h, B, limita):
	vizitat = set()
	vizitat.add(start)
	nivel = set()
	nivel.add(start)
	discrepante = 0

	while True:
		if iteratie_blds(nivel, discrepante, B, h, vizitat, limita) == "SUCCES":
			return "SUCCES"
		discrepante += 1

def iteratie_blds(nivel, discrepante, B, h, vizitat, limita):
	succ = []
	for s in nivel:
		for s_prim in s.get_allowed_moves():
			if s_prim == s_prim.solved():
				print(len(s_prim.moves), len(vizitat),sep=",")
				return "SUCCES"
			if s_prim not in vizitat:
				heappush(succ, (h(s_prim), s_prim))

	if len(succ) == 0:
		return "FAIL"
	
	no_sel_elem = min(B, len(succ))
	if len(vizitat) + no_sel_elem > limita:
		return "FAIL"
	
	if discrepante == 0:
		selectat = nsmallest(B, succ)
		nivel_urm = set()
		for s in selectat:
			nivel_urm.add(s[1])
		vizitat.update(nivel_urm)
		val = iteratie_blds(nivel_urm, 0, B, h, vizitat, limita)
		vizitat = vizitat.difference(nivel_urm).copy()
		return val
	else:
		deja_explorate = B
		while deja_explorate < len(succ):
			n = min(len(succ)- deja_explorate, B)
			selectat = nsmallest(n + deja_explorate, succ)
			nivel_urm = set([s for _, s in selectat[deja_explorate:]])
			vizitat.update(nivel_urm)
			val = iteratie_blds(nivel_urm, discrepante - 1, B, h, vizitat, limita)
			vizitat = vizitat.difference(nivel_urm).copy()
			if val == "SUCCES":
				return "SUCCES"
			deja_explorate += len(nivel_urm)
		
		selectat = nsmallest(B, succ)
		nivel_urm = set([s for _, s in selectat])
		vizitat.update(nivel_urm)
		res = iteratie_blds(nivel_urm, discrepante, B, h, vizitat, limita)
		vizitat = vizitat.difference(nivel_urm)
		return res

	
class NHanoi:
	def __init__(self, no_disks, pegs, moves):
		self.disks = no_disks
		self.pegs = dict()
		self.pegs["A"] = copy(pegs["A"])
		self.pegs["B"] = copy(pegs["B"])
		self.pegs["C"] = copy(pegs["C"])
		self.pegs["D"] = copy(pegs["D"])
		self.moves = copy(moves)

	
	def display(self):
		print(self.pegs)
	
	def clone(self):
		return NHanoi(self.disks, self.pegs, self.moves)

	def apply_move_inplace(self, source, dest):

		self.moves.append((source, dest))
		top = self.pegs[source].pop()
		self.pegs[dest].append(top)
		return self
	
	def apply_move(self, source, dest):
		return self.clone().apply_move_inplace(source, dest)


	def get_allowed_moves(self):
		moves = []
		for source in self.pegs:
			for dest in self.pegs:
				if source != dest:
					if self.pegs[source]:
						if self.pegs[dest]:
							if self.pegs[source][-1] < self.pegs[dest][-1]:
								move = self.apply_move(source, dest)
								moves.append(move)
						else:
							move = self.apply_move(source, dest)
							moves.append(move)
		return moves
	
	def solved(self):
		pegs = dict()
		pegs["A"] = []
		pegs["B"] = []
		pegs["C"] = []
		pegs["D"] = [i for i in range(self.disks, 0, -1)]
		hanoi = NHanoi(self.disks, pegs, self.moves)
		return hanoi
	
	def get_largest_misplaced_disk(self):
		max_disk = 0
		for key in self.pegs:
			if key != 'D' and self.pegs[key] and self.pegs[key][0] > max_disk:
				max_disk = self.pegs[key][0]
		return max_disk
	
	def __eq__(self, other):
		return self.pegs == other.pegs
	def __lt__(self, other):
		return True
	def __hash__(self):
		return hash(tuple(self.pegs))

def hanoi_count_not_placed(state):
	return state.disks - len(state.pegs["D"])
def hanoi_heuristic_largest_misplaced(state):
	return 2**state.get_largest_misplaced_disk() - 1
def hanoi_heuristic(state):
	count = 0
	if state.pegs["D"]:
		for x in state.pegs["A"]:
			count += len([i for i in state.pegs["D"] if x > i])
		for x in state.pegs["B"]:
			count += len([i for i in state.pegs["D"] if x > i])
		for x in state.pegs["C"]:
			count += len([i for i in state.pegs["D"] if x > i])
	else:
		count = state.disks
	return 2*count + hanoi_count_not_placed(state)

def hanoi_largest_dif_intervals(state):
	dist = 0

	lenpegA = len(state.pegs["A"])
	for i in range(lenpegA - 1):
		max_disk = state.pegs["A"][i]
		next_max_disk = state.pegs["A"][i + 1]
		if max_disk - next_max_disk != 1:
			dist += max_disk - next_max_disk 

	lenpegB = len(state.pegs["B"])
	for i in range(lenpegB - 1):
		max_disk = state.pegs["B"][i]
		next_max_disk = state.pegs["B"][i + 1]
		if max_disk - next_max_disk != 1:
			dist += max_disk - next_max_disk 

	lenpegC = len(state.pegs["C"])
	for i in range(lenpegC - 1):
		max_disk = state.pegs["C"][i]
		next_max_disk = state.pegs["C"][i + 1]
		if max_disk - next_max_disk != 1:
			dist += max_disk - next_max_disk 
	
	lenpegD = len(state.pegs["D"])
	for i in range(lenpegD - 1):
		max_disk = state.pegs["D"][i]
		next_max_disk = state.pegs["D"][i + 1]
		if max_disk - next_max_disk != 1:
			dist += max_disk - next_max_disk 


	return dist + state.get_largest_misplaced_disk()**3
		


MLIMIT = 10 * 10 ** 9 # 2 GB RAM limit
setrlimit(RLIMIT_DATA, (MLIMIT, MLIMIT))

sys.setrecursionlimit(10**7) # max depth of recursion
threading.stack_size(2**27)  # new thread will get stack of such size
resource.setrlimit(resource.RLIMIT_STACK, (resource.RLIM_INFINITY, resource.RLIM_INFINITY))



# TESTARE NPuzzle
f = open("files/problems4-easy.txt", "r")
input = f.readlines()
f.close()
problems = [NPuzzle.read_from_line(line) for line in input]

good_pos ={}
for i in range(1, problems[0].N):
	good_pos[i] = divmod(i - 1, problems[0].side)


print("<-------------------------------------->")
print("PROBLEMS 4 EASY")
print("ASTAR")
for i in range(len(problems)):
	print("PROBLEM NO = ", i)
	start = time.time()
	final, discovered = astar(problems[i], manhattan_heuristic)
	end = time.time()
	print(len(final.moves),  discovered,"{:.3f}".format(end - start), sep=",")
	print("TIME = ", end - start)
print("<-------------------------------------->")
print("PROBLEMS 4 EASY")
print("BEAM SEARCH")
for i in range(len(problems)):
	# print("PROBLEM NO = ", i)
	start = time.time()
	final_beam_search = beam_search(problems[i], 100, manhattan_linear_conflicts_heuristic, 100000)
	end = time.time()
	# print(final_beam_search)
	# print("TIME = ", end - start)
	print("{:.3f}".format(end - start))
print("<-------------------------------------->")
print("PROBLEMS 4 EASY")
print("GLDS")
for i in range(len(problems)):
	print("PROBLEM NO = ", i)
	start = time.time()
	final_glds = glds(problems[i], manhattan_linear_conflicts_heuristic, 100000)
	end = time.time()
	print("{:.3f}".format(end - start))
	print(final_glds)
	print("TIME = ", end - start)
print("<-------------------------------------->")
print("BLDS")
print("PROBLEMS 4 EASY")
for i in range(len(problems)):
	print("PROBLEM NO = ", i)
	start = time.time()
	final_blds = blds(problems[i], manhattan_linear_conflicts_heuristic, 100, 100000)
	end = time.time()
	print("{:.3f}".format(end - start))
	print(final_blds)
	print("TIME = ", end - start)
print("<-------------------------------------->")


f = open("files/problems5-easy.txt", "r")
input = f.readlines()
f.close()
problems = [NPuzzle.read_from_line(line) for line in input]

good_pos ={}
for i in range(1, problems[0].N):
	good_pos[i] = divmod(i - 1, problems[0].side)

print(good_pos)


print("<-------------------------------------->")
print("PROBLEMS 5 EASY")
print("ASTAR")
for i in range(len(problems)):
	print("PROBLEM NO = ", i)
	start = time.time()
	final, discovered = astar(problems[i], manhattan_heuristic)
	end = time.time()
	print(len(final.moves),  discovered,"{:.3f}".format(end - start), sep=",")
	print("TIME = ", end - start)
print("<-------------------------------------->")
print("PROBLEMS 5 EASY")
print("BEAM SEARCH")
for i in range(len(problems)):
	print("PROBLEM NO = ", i)
	# problems[i].display()
	start = time.time()
	final_beam_search = beam_search(problems[i], 1000, manhattan_heuristic, 500000)
	end = time.time()
	print("{:.3f}".format(end - start))
	print(final_beam_search)
	print("TIME = ", end - start)
print("<-------------------------------------->")
print("PROBLEMS 5 EASY")
print("GLDS")
for i in range(len(problems)):
	print("PROBLEM NO = ", i)
start = time.time()
final_glds = glds(problems[4], manhattan_heuristic, 500000)
end = time.time()
	print(final_glds)
	print("TIME = ", end - start)
print("{:.3f}".format(end - start))
print("<-------------------------------------->")
print("PROBLEMS 5 EASY")
print("BLDS")
for i in range(len(problems)):
	print("PROBLEM NO = ", i)
	start = time.time()
	final_blds = blds(problems[i], manhattan_heuristic, 1000, 500000)
	end = time.time()
	print("{:.3f}".format(end - start))
	print(final_blds)
	print("TIME = ", end - start)
print("<-------------------------------------->")


f = open("files/problems6-easy.txt", "r")
input = f.readlines()
f.close()
problems = [NPuzzle.read_from_line(line) for line in input]

good_pos ={}
for i in range(1, problems[0].N):
	good_pos[i] = divmod(i - 1, problems[0].side)
print(good_pos)

print("<-------------------------------------->")
print("PROBLEMS 6 EASY")
print("ASTAR")
for i in range(len(problems)):
	print("PROBLEM NO = ", i)
	start = time.time()
	final, discovered = astar(problems[i], manhattan_heuristic)
	end = time.time()
	print(len(final.moves),  discovered,"{:.3f}".format(end - start), sep=",")
	print("TIME = ", end - start)
print("<-------------------------------------->")
print("PROBLEMS 6 EASY")
print("BEAM SEARCH")
for i in range(len(problems)):
	print("PROBLEM NO = ", i)
	start = time.time()
	final_beam_search = beam_search(problems[i], 1000, manhattan_heuristic, 100000)
	end = time.time()
	print("{:.3f}".format(end - start))
	print(final_beam_search)
	print("TIME = ", end - start)
print("<-------------------------------------->")
print("PROBLEMS 6 EASY")
print("GLDS")
for i in range(len(problems)):
	print("PROBLEM NO = ", i)
	start = time.time()
	final_glds = glds(problems[i], manhattan_heuristic, 100000)
	end = time.time()
	print("TIME = ", end - start)
	print(final_glds)
	print("TIME = ", end - start)
print("<-------------------------------------->")
print("PROBLEMS 6 EASY")
print("BLDS")
for i in range(len(problems)):
	print("PROBLEM NO = ", i)
	start = time.time()
	final_blds = blds(problems[i], manhattan_heuristic, 1000, 100000)
	end = time.time()
	print("{:.3f}".format(end - start))
	print(final_blds)
	print("TIME = ", end - start)
print("<-------------------------------------->")


f = open("files/problems4.txt", "r")
input = f.readlines()
f.close()
problems = [NPuzzle.read_from_line(line) for line in input]

good_pos ={}
for i in range(1, problems[0].N):
	good_pos[i] = divmod(i - 1, problems[0].side)


print("<-------------------------------------->")
print("PROBLEMS 4")
print("ASTAR")
for i in range(len(problems)):
	print("PROBLEM NO = ", i)
	astar(problems[2], manhattan_linear_conflicts_heuristic)
print("<-------------------------------------->")
print("PROBLEMS 4")
print("BEAM SEARCH")
for i in range(len(problems)):
	print("PROBLEM NO = ", i)
	start = time.time()
	final_beam_search = beam_search(problems[i], 1000, manhattan_heuristic, 100000)
	end = time.time()
	print("{:.3f}".format(end - start))
	print(final_beam_search)
	print("TIME = ", end - start)
print("<-------------------------------------->")
print("PROBLEMS 4")
print("GLDS")
for i in range(len(problems)):
	print("PROBLEM NO = ", i)
	start = time.time()
	final_glds = glds(problems[i], manhattan_heuristic, 100000)
	end = time.time()
	print("{:.3f}".format(end - start))
	print(final_glds)
	print("TIME = ", end - start)
print("<-------------------------------------->")
print("PROBLEMS 4")
print("BLDS")
for i in range(len(problems)):
	print("PROBLEM NO = ", i)
	start = time.time()
	final_blds = blds(problems[i], manhattan_heuristic, 500, 100000)
	end = time.time()
	print("{:.3f}".format(end - start))

	print(final_blds)
	print("TIME = ", end - start)
print("<-------------------------------------->")



f = open("files/problems5.txt", "r")
input = f.readlines()
f.close()
problems = [NPuzzle.read_from_line(line) for line in input]

good_pos ={}
for i in range(1, problems[0].N):
	good_pos[i] = divmod(i - 1, problems[0].side)


print("<-------------------------------------->")
print("PROBLEMS 5")
print("ASTAR")
for i in range(len(problems)):
	print("PROBLEM NO = ", i)
	astar(problems[i], manhattan_linear_conflicts_heuristic)
print("<-------------------------------------->")
print("PROBLEMS 5")
print("BEAM SEARCH")
for i in range(len(problems)):
	print("PROBLEM NO = ", i)
	start = time.time()
	final_beam_search = beam_search(problems[i], 100, manhattan_heuristic, 500000)
	end = time.time()
	print("{:.3f}".format(end - start))
	print(final_beam_search)
	print("TIME = ", end - start)
print("<-------------------------------------->")
print("PROBLEMS 5")
print("GLDS")
for i in range(len(problems)):
	print("PROBLEM NO = ", i)
start = time.time()
final_glds = glds(problems[4], manhattan_heuristic, 500000)
end = time.time()
print("{:.3f}".format(end - start))

	print(final_glds)
	print("TIME = ", end - start)
print("<-------------------------------------->")
print("PROBLEMS 5")
print("BLDS")
for i in range(len(problems)):
	print("PROBLEM NO = ", i)
	start = time.time()
	final_blds = blds(problems[i], manhattan_heuristic, 1000, 500000)
	end = time.time()
	print("{:.3f}".format(end - start))
	print(final_blds)
	print("TIME = ", end - start)
print("<-------------------------------------->")


f = open("files/problems6.txt", "r")
input = f.readlines()
f.close()
problems = [NPuzzle.read_from_line(line) for line in input]

good_pos ={}
for i in range(1, problems[0].N):
	good_pos[i] = divmod(i - 1, problems[0].side)

print(good_pos)
# # print("<-------------------------------------->")
# print("PROBLEMS 6")
# print("ASTAR")
# for i in range(len(problems)):
# 	print("PROBLEM NO = ", i)
# 	astar(problems[i], manhattan_linear_conflicts_heuristic)
print("<-------------------------------------->")
print("PROBLEMS 6")
print("BEAM SEARCH")
for i in range(len(problems)):
	print("PROBLEM NO = ", i)
	start = time.time()
	final_beam_search = beam_search(problems[i], 1000, manhattan_heuristic, 1000000)
	end = time.time()
	print("{:.3f}".format(end - start))
	print(final_beam_search)
	print("TIME = ", end - start)
print("<-------------------------------------->")
print("PROBLEMS 6")
print("GLDS")
for i in range(len(problems)):
print("PROBLEM NO = ", 4)
start = time.time()
final_glds = glds(problems[4], manhattan_heuristic, 1000000)
end = time.time()
print("{:.3f}".format(end - start))
print(final_glds)
print("TIME = ", end - start)
print("<-------------------------------------->")
print("PROBLEMS 6")
print("BLDS")
for i in range(len(problems)):
	print("PROBLEM NO = ", i)
start = time.time()
final_blds = blds(problems[4], manhattan_heuristic, 1000, 1000000)
end = time.time()
print("{:.3f}".format(end - start))
	print(final_blds)
	print("TIME = ", end - start)
print("<-------------------------------------->")


TESTARE HANOI
pegs = dict()
moves = []
pegs["A"] = [i for i in range(10, 0, -1)]
pegs["B"] = []
pegs["C"] = []
pegs["D"] = []
hanoi = NHanoi(10, pegs, moves)
hanoi.display()
start = time.time()
final, discovered = astar(hanoi, hanoi_largest_dif_intervals)
final_glds = glds(hanoi, hanoi_largest_dif_intervals, 500000)
final_beam_search = beam_search(hanoi, 1000, hanoi_largest_dif_intervals, 1000000)
final_blds = blds(hanoi, hanoi_largest_dif_intervals, 1000, 1000000)
end = time.time()
print("{:.3f}".format(end - start))
print(len(final.moves),  discovered,"{:.3f}".format(end - start), sep=",")

print(final_blds)

astar(hanoi, hanoi_heuristic)