# Boundary kernel and radical covariance of the scalar Jacquet integral

Author: Worker 643.

This internal statement unit isolates two consequences of the published
`Shahidi.Geometry`, `Shahidi.Characters`, and `Shahidi.JacquetIntegral`
definitions. It supplies proposition definitions, without proofs. Its
provenance is the literal scalar integrand and additive rectangular subgroup
already defined in those modules; it introduces no new matrix, measure, or
character convention.

`IntertwiningJacquetBoundaryStatement` quantifies over every topological
field, continuous unitary additive character, and positive ranks `m+1,n+1`.
For the actual exchanged-radical coordinate `x`, an `(n+1)` by `(m+1)`
matrix, it asserts

```text
intertwiningCharacter(x) = psi(x(last n,0)),
intertwiningJacquetKernel(x) = psi(-x(last n,0)).
```

The entry is the last row and first column of the rectangular coordinate,
with no transpose. The ambient group remains of rank `(m+1)+(n+1)`.
`swapRank` in the existing definition changes only the total-rank expression
and preserves the numerical positions of matrix entries; it is separate
from the block Weyl permutation. Thus this statement fixes the inverse
character sign needed when using the existing scalar Jacquet integrand.

`IntertwiningJacquetTranslationStatement` uses the same actual group
functions and arbitrary algebraic complex coefficient module as
`jacquetIntegrand`. It additionally assumes a topological ring structure,
a Borel measurable field, and a supplied measure on the rectangular space
invariant under right addition. A product additive Haar measure is an
instance of this hypothesis. It requires no selected normalization,
regularity, sigma finiteness, or topology on the coefficient module.
For right translation `f_y(g) = f(g u'(y))`, it asserts the pointwise identity

```text
I(f_y)(x) = character(y) * I(f)(x+y).
```

Here `I` is the published `jacquetIntegrand`, using the all-positive block
Weyl representative and the inverse character. If `I(f)` is integrable,
then `I(f_y)` is integrable, and the ordinary Bochner integral is multiplied
by the positive character of `y`. Integrability of the original integrand
is an explicit premise of the integral assertion, with no convergence
claim for general group functions.

`JacquetRadicalCovarianceStatement` is the conjunction of the two closed
propositions, with independent field and coefficient universes. It is an
internal scalar prerequisite for the two-block Whittaker construction.
It does not assert covariance under the rest of the full upper-unipotent
group, stability or existence of induced cell sections, extension of a
functional, nonvanishing, Fourier surjectivity, or the JPSS extension formula.
