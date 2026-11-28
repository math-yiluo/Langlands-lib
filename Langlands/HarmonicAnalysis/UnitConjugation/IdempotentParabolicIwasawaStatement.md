# Compact Iwasawa factorization for an idempotent parabolic

For a finite-dimensional semisimple algebra \(A\) over a
characteristic-zero nonarchimedean local field \(F\), let \(e\)
be an idempotent and \(P\) the subgroup `parabolicUnits` of \(A^\times\).
It is the group of units \(p\) with \((1-e)pe=0\). The topology
on \(A\) is its \(F\)-module topology.

`IdempotentParabolicIwasawaStatement` asserts the existence of a
compact open subgroup \(K\) of \(A^\times\) such that every
\(g\in A^\times\) can be written \(g=pk\) with \(p\in P\) and \(k\in K\).
The assertion includes finite products and division-algebra matrix
factors in \(A\).

## Source

In Harish-Chandra, *Admissible invariant distributions on reductive
p-adic groups*, University Lecture Series 16, 1999, §1.2, p. 7,
the compact open subgroup used for parabolic descent gives \(G=KP\).
Inversion gives the product order \(G=PK\) for left centralizer
quotients. The idempotent parabolic corresponds to the cocharacter
\(t\mapsto te+(1-e)\).
Conjugation by this cocharacter fixes the diagonal blocks and
multiplies the upper and opposite blocks by \(t\) and \(t^{-1}\).
The subgroup of units for which the conjugation orbit extends
to \(t=0\) is thus the upper triangular unit subgroup.
