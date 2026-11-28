# Schwartz majorants from rapid bounds

This internal analytic helper supports the construction of a smooth majorant
from a family of rapid polynomial bounds. Its provenance is the definition
of Schwartz maps and Mathlib's theorem on smooth series.

`exists_schwartz_tsum` proves that a series of Schwartz functions whose
seminorms are summable for every weight and derivative order defines a
Schwartz function by pointwise summation. The zeroth-weight seminorms bound
each derivative uniformly, so the smooth-series theorem applies. Interchanging
derivatives with the series and applying the triangle inequality gives every
weighted derivative bound.

`dilation_decay_le`, `dilate` and `seminorm_dilate_le` control the operation
`f(x) ↦ f(x/R)` for `R ≥ 1`. The derivative of order `n` gains the factor
`R⁻ⁿ ≤ 1`, while the weight of order `k` costs `Rᵏ`. These results include
zero-dimensional spaces and order zero.

`exists_tail_coefficients` treats an arbitrary family of points `z i` and
nonnegative weights `w i` with uniform bounds on
`(1 + ‖z i‖)^N * w i` for every natural `N`. For each `j` it takes the
supremum, with zero included, of the weights satisfying
`2^j ≤ 1 + ‖z i‖`. These coefficients are nonnegative, dominate the
corresponding tails, and have summable moments against `2^((j+1)*k)`
for every natural `k`. The rapid bound of order `k+1` compares that
weighted series with a geometric series.

`exists_nonneg_schwartz_majorant` assumes a finite-dimensional real normed
space. It chooses a smooth bump equal to one on the unit ball, dilates it
by the radii `2^(j+1)`, multiplies it by those coefficients, and sums the
resulting nonnegative Schwartz functions. The seminorm bound on dilations
and the summable coefficient moments allow `exists_schwartz_tsum` to apply.
For each family point, two successive powers of two bracket `1 + ‖z i‖`.
The bump at the upper radius equals one there, and its coefficient
dominates `w i`. That single nonnegative summand gives the desired
pointwise majorization. No continuity of the family or its supremum is used.

`exists_nonneg_schwartz_majorant_of_bump` carries out the same construction
with a prescribed nonnegative Schwartz bump equal to one on the unit ball.
It also proves that if two points give equal values under every dilation
of that bump by a radius at least one, the majorant takes equal values at
those points. This will allow local-magnitude symmetries to be preserved
when choosing the bump for an adelic application.

These are internal analytic constructions from Mathlib's bump, smooth-series
and Schwartz-space results. The file asserts no adelic gauge or integral bound.

`exists_schwartz_tsum_with_seminorm` records the bound on every seminorm of the sum by the sum of the corresponding seminorms. The bound follows from the same termwise derivative estimate that gives rapid decrease.
