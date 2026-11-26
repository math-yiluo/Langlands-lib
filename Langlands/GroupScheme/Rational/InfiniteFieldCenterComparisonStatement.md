# The center on rational points over an infinite field

`Langlands.GroupScheme.InfiniteFieldCenterComparisonStatement` says that
for an infinite field \(k\) and a connected reductive group scheme \(G\)
over \(k\), the equality \(Z(G)(k) = Z(G(k))\) holds as subgroups of \(G(k)\).

It uses `RationalCenterComparison G`. The left side is `schemeCenterPoints G`,
which evaluates the full center functor at the identity test \(\operatorname{Spec} k\).
A point in this subgroup commutes with all points on every test scheme after
pullback. The right side is `Subgroup.center (rationalPoints G)`.

## Source

J. S. Milne, *Algebraic Groups* (2017), Propositions 1.92–1.93, printed
pp. 33–34 (PDF pp. 49–50), and Theorem 17.93(b), printed p. 382 (PDF p. 398).
Registered source `milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.

Take \(H = G\) and \(k' = k\) in Proposition 1.93. Smoothness follows from
connected reductivity, and Theorem 17.93(b) gives the required density of
\(G(k)\) over an infinite field. Proposition 1.92 identifies the center as
the all-test centralizer of \(G\) in itself.
