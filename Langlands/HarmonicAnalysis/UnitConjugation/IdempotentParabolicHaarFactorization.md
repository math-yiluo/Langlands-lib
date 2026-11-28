# Haar integration in parabolic and compact coordinates

Let \(A\) be a finite-dimensional algebra with locally compact, Hausdorff,
second-countable topological ring structure. For an idempotent \(e\), let
\(M\) be its centralizer algebra, \(N=eA(1-e)\) its upper corner and \(P\)
its upper triangular unit subgroup. Suppose \(K\) is a compact open subgroup
of \(A^\times\) with \(A^\times=PK\). Give the groups their Borel measurable
structures. Use left Haar measures on \(A^\times\) and \(M^\times\), additive
Haar measure on \(N\), and the restriction of ambient Haar on \(K\). The Levi
and upper-corner measures are assumed s-finite.

`IdempotentParabolicHaarFactorizationStatement` says that the product of
the Levi, upper-corner and compact subgroup measures pushes forward along
\[
 (m,Z,k)\longmapsto m(1+Z)k
\]
to a positive finite multiple of the ambient measure. The factor is the
product mass of the preimage of \(P\cap K\) in the Levi–unipotent coordinates.
This preimage is compact because \(P\) is closed and multiplication gives
a homeomorphism onto it. It is open and contains the identity coordinates,
so its product Haar mass is positive.

The proof transports the Levi and upper-corner measures to the subgroup
images of \(M^\times\) and \(1+N\). Left translations on \(P\) act by
translation on the Levi coordinate and by a translation depending on the
Levi coordinate in the unipotent fiber. The product measure is therefore
left invariant in these coordinates. The factorization integral in
`CompactFactorizationBochner` identifies its product with restricted Haar
on \(K\), pushed forward to \(A^\times\), with the specified multiple of
ambient Haar. Transport and reordering of the product measures give the
stated order of integration.

Harish-Chandra uses this Haar factorization with the normalizations of
the orbital quotient measures in *Admissible invariant distributions on
reductive \(p\)-adic groups*, §1.2, printed p. 7. The scalar records the
effect of arbitrary choices of the factor measures.
