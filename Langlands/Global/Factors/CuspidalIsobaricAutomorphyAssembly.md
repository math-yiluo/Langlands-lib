# Assembly from prescribed local constituent embeddings

`HasIsobaricConstituentEmbeddings` gives the hypotheses for the last step
of the all-places isobaric construction. A single irreducible automorphic
operator subquotient receives an injective intertwiner from every chosen
finite representation. At each real or complex place the data supply
parameters of the actual cuspidal summands, a Langlands-ordered permutation
of their concatenation, and an embedding of an irreducible quotient of that
standard module. The quotient is given by a simultaneous compact- and
Lie-stable subspace, with the induced actions on the quotient.

`isCuspidalIsobaricSum_of_constituentEmbeddings` assumes the chosen finite
representations are the local isobaric sums and proves the published
`IsCuspidalIsobaricSum` predicate on the given global subquotient. The
finite clause uses the given embeddings. Each archimedean clause composes
the quotient projection with the given embedding. Surjectivity of the
projection makes this composite have the same image as the embedding,
which is nonzero and irreducible. The Library's real and complex
quotient-to-place lemmas implement this composition.

This is the extraction after the global realization in Getz and Hahn,
*An Introduction to Automorphic Representations* (2024), proof of Theorem
10.7.5, printed p. 288 (PDF p. 300). The supplied embeddings have the intended
form of those obtained from the tensor factors in Langlands,
*On the notion of an automorphic representation* (1979), Lemma 1 and
Proposition 2, printed pp. 203–204 (PDF pp. 198–199).
