# Continued operators through a nested pair of parabolics

`nestedContinuedOperators_scaled_square` compares the actual ambient
continuation with a separately specified lower compact continuation
when both original operators represent the standard integrals on a
nonempty open set in the ambient full domain. The lower parameter is
written in the same unramified characters as the ambient parameter.
The compact restriction maps are those of `compactStagesRestriction`.
The scalar is the ratio of the ambient quotient measure pushed to the
lower quotient to the lower quotient measure.

`hasNestedCompactContinuation` produces the lower operator at the exact
pushed-forward measure. `RepresentsStandardIntegral.smul_nnreal` and
`RepresentsStandardIntegral.eq` identify it on the original open set
with the scalar multiple of the operator normalized at the lower
measure. The fixed compact restriction square then persists at the
common regular points by `rationalOperatorContinuationData_natural`.

The source interpretation is Waldspurger IV.1(14), printed p. 284,
source `waldspurger-2003-plancherel`, SHA-256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
