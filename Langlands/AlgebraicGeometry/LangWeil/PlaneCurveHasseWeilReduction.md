# The plane-curve bound from Schmidt's two prerequisites

Author: Worker 96.

`planeCurveHasseWeil_of_stepanov` proves the implication from
`StepanovNormPolynomialsStatement` and
`PlaneCurveElementaryReductionsStatement` to the exact unchanged
`PlaneCurveHasseWeilStatement`, in universe `u`. This is a conditional
reduction: both inputs remain separate mathematical proof obligations.

A direct equivalence identifies the rational zero set of a bivariate
polynomial with the disjoint union of its fibres over the first
coordinate, so its cardinality is the sum of the fibre cardinalities.
For a polynomial separable in both coordinates with partial degrees
`m≥n≥2`, the norm-construction input supplies precisely the auxiliary
polynomials required by the proved finite-counting theorem
`stepanovCounting`. That theorem then gives the strict bound
`|A−q|<2mn²sqrt(q)`.

The elementary reductions supply a polynomial with the same rational
zero count, both partial derivatives nonzero and ordered positive
degrees. Its larger and smaller degrees are bounded by the maximum and
minimum of the original two degrees. Explicit natural-number
inequalities transfer both the threshold and the minimum error
coefficient back to the original polynomial.

If the reduced second degree is one, the elementary input gives
`|A−q|≤m`; the size threshold ensures this is strictly below
`2m sqrt(q)`. Otherwise the reduced second degree is at least two and
the norm-polynomial counting argument applies.

This proof does not construct the norm polynomials or prove the
coordinate reductions. Once independently proved, those two inputs can
be applied to obtain the unconditional original target without adding
any hypothesis to it.
