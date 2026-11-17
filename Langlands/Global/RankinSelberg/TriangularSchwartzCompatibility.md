# Compatibility of simple-root Schwartz data

This internal helper applies the coordinate symmetries of the constructed
Schwartz–Bruhat majorant to triangular matrices in the standard compact
subgroup. Multiplying a diagonal tuple by their diagonal units preserves every
real and complex magnitude of the adjacent ratios. At finite places the
resulting adjacent ratios and their inverses are integral, so multiplication
preserves each denominator-integrality condition in both directions.

The proof uses the archimedean and finite diagonal facts proved in
`TriangularCompactCoordinates`. Consequently any function with the stated
coordinate symmetries takes equal values on the two simple-root rows. This
is a compatibility lemma for the later continuous descent; it asserts no
analytic estimate.
