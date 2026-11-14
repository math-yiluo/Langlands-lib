# Galois differences of transporters between descended tori

This module proves the algebraic step needed after constructing a common
special apartment. It does not assert existence of that apartment. All
declarations are in arbitrary universe `u`.

Let \(k\subseteq K\) be any extension of fields in universe `u`, let \(G/k\)
be a group scheme, and let \(i:T\to G\) and \(j:T'\to G\) be homomorphisms
from commutative group schemes over \(k\). Suppose \(g\in G_K(K)\) and
\(e:T_K\simeq T'_K\) satisfy
\[
 i_K \mathbin{\gg} \operatorname{Int}(g)
   = e \mathbin{\gg} j_K
\]
in Lean's composition convention. Then every
\(\sigma\in\operatorname{Aut}(K/k)\) satisfies
\[
 g^{-1}\sigma(g)\in\texttt{normalizerPoints}\ i_K.
\]
Neither source need be a torus. The argument needs no monomorphism,
reductivity, local-field, valuation or finite-extension hypothesis.

This is an internal consequence of published Library algebra. First,
`StarActionIndependence.IsConjugatingPoint.baseChange_descent` in
`Langlands.GroupScheme.Reductive.StarActionIndependenceProof` transports
the supplied conjugacy by the coefficient base map and the canonical
descent isomorphisms. Its point is
`rationalConjugate k K G σ g` by
`rationalConjugate_eq_baseChange_descent` in
`Langlands.GroupScheme.Rational.NormalizerGaloisAction`.
Both the original point and its coefficient conjugate therefore
transport \(i_K\) to \(j_K\). Applying
`inv_mul_mem_normalizerPoints_of_transporters` in
`Langlands.GroupScheme.Rational.TorusTransporterOrbit`, with those two
transporters in the indicated order, gives the conclusion for the
actual embedded source group.

The module also contains two generic helpers in the
`StarActionIndependence` namespace.
`IsConjugatingPoint.of_point_eq` substitutes an equal point in a conjugacy
equation, by equality elimination.
`IsConjugatingPoint.baseChange_descent_of_eq` applies the published
`IsConjugatingPoint.baseChange_descent` and then this substitution. Its
bases are arbitrary schemes, and both source commutative group schemes
are transported through their own descent isomorphisms. The final
field-extension theorem uses this second helper with
`rationalConjugate_eq_baseChange_descent`, then applies the published
two-transporter normalizer lemma. This expresses coefficient transport
without rewriting the expanded point inside the entire conjugacy equation.

These are derived internal lemmas. Their only mathematical inputs are the
Library declarations named above; no additional assertion from the book
is used. They are supporting code for a later proof of the common-apartment
statement, not a proof of that statement or of the transporter target.
