# Constituent automorphy for one block

When there is one block, normalized induction from the full group is
equivalent to the inducing representation. Here
`singleBlockNormalizedProductEquiv` gives that equivalence at each
finite place, and the reindexing of the single block is the identity.
Every irreducible subquotient of the resulting irreducible local
representation is equivalent to it.

Use the zero-denominator quotient of the original cuspidal realization
for \(Q\). `cuspidalLocalInclusion` includes each supplied local
component into the full cuspidal realization and then into that
quotient using the finite part of the quotient equivalence.
Composing with the local equivalences gives the requested embeddings
into this one \(Q\).

`singleBlockAutomorphy_of_card_eq_one` applies this construction to
the target statement's indexed family. The rank sum forces the size of
the unique block to equal the ambient rank, and the inducing family on
`Fin 1` is constant.

This is the single-block case of R. P. Langlands, *On the notion of an
automorphic representation* (1979), Lemma 1 and Proposition 2,
printed pp. 203–204, PDF pp. 198–199 of Corvallis Part I
(`langlands-1979-notion-automorphic-representation`). The
normalization is the Library's canonical normalized product induction.
