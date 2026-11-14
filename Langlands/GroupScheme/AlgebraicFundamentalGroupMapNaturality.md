# Naturality of induced algebraic fundamental-group maps

This internal module proves the full
`AlgebraicFundamentalGroupMapStatement` from the explicit hypothesis
`AlgebraicFundamentalGroupComparisonStatement`. It does not establish the
comparison statement.

The geometric construction starts with a source conjugator and two target
torus factorizations. Its image in the target group conjugates the first
containing maximal torus. Relative conjugacy of tori containing the resulting
common image supplies a second conjugator. Their product induces a target
torus isomorphism compatible with the source isomorphism and both
factorizations. `factorizationComparisonAlongConjugation` selects these proved
data.

Assuming canonical comparisons, the previously constructed induced map exists,
so epsilon selection satisfies its defining law. A torus factorization over
the original field, naturality of Galois transport, and equivariance of
comparison prove Galois equivariance of every induced map. For a change of
source presentation, the chosen comparison supplies an actual conjugator.
The compatible target conjugator above and the two comparison formulas on
representatives prove simultaneous source and target compatibility.

The final theorem combines these results with quotient extensionality to
prove unique existence, the selected-map specification, equivariance, and
presentation compatibility. This is a derived Library construction supporting
Kaletha–Prasad, Lemma 11.3.6; the implementation adds no external assertion.
