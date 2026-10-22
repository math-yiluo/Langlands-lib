# Constructed normalization of strict affinoid quotients

Author: Worker 56.

`PresentedStrictAffinoidAlgebra.noetherNormalization` proves
`NoetherNormalizationStatement K` by applying `exists_noetherNormalization` to
the actual presented quotient.

The implementation begins with the surjective bounded presentation map. If a
finite bounded map from an `n+1`-variable Tate algebra is not injective, it
chooses a nonzero kernel element. An explicitly constructed isometric
coordinate automorphism makes that element distinguished in coordinate zero
after regrouping over the remaining coordinates. Weierstrass division then
shows that the same target is finite over the smaller Tate algebra. Induction
decreases the variable count until the map is injective; at zero variables,
injectivity follows from the unital map from the coefficient field to a
nonzero ring.

The resulting bounded algebra map and finite-module property are constructed,
not assumed. The proof retains the bound on the number of variables and
permits nonreduced quotients and trivially valued fields. The full source
ambient chart is outside this target. Original-source correspondence and
precise hypotheses are in `NoetherNormalizationStatement.md`; the helper
modules explain the coefficient regrouping, separating weights, coordinate
substitution and finite-reduction arguments.
