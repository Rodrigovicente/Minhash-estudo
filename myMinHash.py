
from __future__ import division
import os
import re
import random
import time
import binascii
import xml.etree.ElementTree as ET
from bisect import bisect_right
from heapq import heappop, heappush


# This is the number of components in the resulting MinHash signatures.
# Correspondingly, it is also the number of random hash functions that
# we will need in order to calculate the MinHash.
numHashes = 10;

# parser = ET.XMLParser(encoding="utf-8")
# tree = ET.fromstring('cfc-xml/cf74.xml', parser=parser)
tree = ET.parse('cfc-xml/cf74.xml', ET.XMLParser(encoding='utf-8'))
root = tree.getroot()

# número total de documentos
# numDocs = len(root.findall('RECORD'))
numDocs = 0

docNames = []
word_map = []
docsAsShingleSets = {};

totalShingles = 0

# PARA CADA DOCUMENTO NO ARQUIVO
for record in root.findall('RECORD'):

	docID = int(record.find('RECORDNUM').text)

	# normaliza
	if record.find('ABSTRACT') != None:
		record = record.find('ABSTRACT').text.lower()
		docNames.append(docID)
	elif record.find('EXTRACT') != None:
		record = record.find('EXTRACT').text.lower()
		docNames.append(docID)
	else:
		print(record.find('RECORDNUM').text, " -- ", record.find('ABSTRACT'), " / ", record.find('EXTRACT'))
		continue

	numDocs = numDocs + 1

	# words = record.find('ABSTRACT').text.lower().replace(".", "").replace(",", "").split()

	"""
	TRANSFORMA O TEXTO EM LISTA DE PALAVRAS
	(Para minhash e indice invertido)
	"""
	word_list = []
	wcurrent = []
	windex = None

	windex = 0
	for i, c in enumerate(record):
		if c.isalnum():
			wcurrent.append(c)
		elif wcurrent:
			word = u''.join(wcurrent)
			word_map.append((windex, word))
			word_list.append(word)
			wcurrent = []
		windex = i

	if wcurrent:
		word = u''.join(wcurrent)
		word_map.append((windex, word))
		word_list.append(word)

	""" """

	"""
	CRIA O INDICE INVERTIDO
	"""
	inverted_index_t0 = time.time()

	inverted = {}

	for index, word in word_map :
		inverted.setdefault(word, [])
		locations = inverted[word]
		locations.append(index)

	inverted_index_deltat = time.time() - inverted_index_t0;

	""" """
	# print indice invertido
	# for keys, locations in inverted.items():
	# 	print(keys, " --> ", locations)

	"""
	CRIA OS SHINGLES
	"""
	minhash_shingles_t0 = time.time()

	shinglesInDoc = set()

	for index in range(0, len(word_list) - 2):

		# usa tres palavras consecutivas para gerar o shingle
		shingle = word_list[index] + " " + word_list[index + 1] + " " + word_list[index + 2]

		crc = binascii.crc32(shingle.encode()) & 0xffffffff

		shinglesInDoc.add(crc)


	docsAsShingleSets[docID] = shinglesInDoc


	minhash_shingles_deltat = time.time() - minhash_shingles_t0

	""" """


"""
MAPEAMENTO DA MATRIZ
Função para mapear as duas coordenadas da matriz triangular em um indice de array (relativo à matriz)
"""

def getTriangleIndex(i, j):
  # If i == j that's an error.
	if i == j:
		sys.stderr.write("Can't access triangle matrix with i == j")
		sys.exit(1)
	# If j < i just swap the values.
	if j < i:
		temp = i
		i = j
		j = temp

	# Calculate the index within the triangular array.
	# This fancy indexing scheme is taken from pg. 211 of:
	# http://infolab.stanford.edu/~ullman/mmds/ch6.pdf
	# But I adapted it for a 0-based index.
	# Note: The division by two should not truncate, it
	#       needs to be a float.
	k = int(i * (numDocs - (i + 1) / 2.0) + j - i) - 1

	return k

""" """


# Record the maximum shingle ID that we assigned.
maxShingleID = 2**32-1

# We need the next largest prime number above 'maxShingleID'.
# I looked this value up here:
# http://compoasso.free.fr/primelistweb/page/prime/liste_online_en.php
nextPrime = 4294967311


"""
GERA LISTA DE COEFICIENTES
que serão usados na função de hash
h(x) = (a*x + b) % c
"""

def pickRandomCoeffs(k):
	randList = []

	while k > 0:
		randIndex = random.randint(0, maxShingleID)

		while randIndex in randList:
			randIndex = random.randint(0, maxShingleID)

		randList.append(randIndex)
		k = k - 1

	return randList

# armazena a lista de coeficientes que será reutilizada para cada documento (a função de hash usada em cada documento é a mesma)
coeffA = pickRandomCoeffs(numHashes)
coeffB = pickRandomCoeffs(numHashes)

""" """


"""
GERA AS ASSINATURAS DOS DOCUMENTOS
"""
minhash_signatures_t0 = time.time()

# Lista de assinaturas de cada documento
signatures = []

# Ao invés de permutar os shingles, é apenas aplicada uma função de hash
# nos shingles dos documentos. Então pegamos o menor valor de hash resultante,
# que corresponde ao indice do primeiro shingle que seria encontrado se fosse
# feita uma permutação.

# para cada documento
for docID in docNames:

	# conjunto de shingles no documento atual
	shingleIDSet = docsAsShingleSets[docID]

	signature = []

	# para cada função de hash
	for i in range(0, numHashes):

		# inicialmente armazena um número maior que o maior índice possível
		minHashCode = nextPrime + 1

		# para cada shingle no documento
		for shingleID in shingleIDSet:

			# aplica a função de hash
			hashCode = (coeffA[i] * shingleID + coeffB[i]) % nextPrime

			# escolhe a com menor valor no índice calculado pela função de hash
			if hashCode < minHashCode:
				minHashCode = hashCode

    	# adiciona este menor valor de índice à assinatura
		signature.append(minHashCode)

	# armazena a assinatura do documento
	signatures.append(signature)

minhash_signatures_deltat = time.time() - minhash_signatures_t0

""" """


"""
GERA A TABELA DE SIMILARIDADES USANDO MINHASH
"""
minhash_table_t0 = time.time()

# número de elementos na tabela triangular de similaridades
numElems = int(numDocs * (numDocs - 1) / 2)

# tabela de similaridade de jaccard estimada
estJSim = [0 for x in range(numElems)]

# para cada documento
for i in range(0, numDocs):
  # pega a assinatura deste documento
  signature1 = signatures[i]

  # para cada um dos outros documentos
  for j in range(i + 1, numDocs):

    # pega a assinatura deste documento
    signature2 = signatures[j]

    count = 0
    # conta o número de posições iguais entre as duas assinaturas
    for k in range(0, numHashes):
      count = count + (signature1[k] == signature2[k])

    # armazena a porcentagem correspondente às posições iguais na tabela
    estJSim[getTriangleIndex(i, j)] = (count / numHashes)

minhash_signatures_deltat = time.time() - minhash_signatures_t0

""" """


threshold = 0.05

# compara apenas documentos que não foram comparados ainda
for i in range(0, numDocs):
	for j in range(i + 1, numDocs):
		estJ = estJSim[getTriangleIndex(i, j)]

		if estJ > threshold:

			# Calcula a real similaridade de jaccard
			s1 = docsAsShingleSets[docNames[i]]
			s2 = docsAsShingleSets[docNames[j]]
			if len(s1.union(s2)):
				J = (len(s1.intersection(s2)) / len(s1.union(s2)))
				print (docNames[i], " --> ", docNames[j], "\t", estJ,"\t", J)
			else:
				print (docNames[i], " --> ", docNames[j], "\t", estJ)


print (".")
