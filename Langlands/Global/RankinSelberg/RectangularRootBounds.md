# Polynomial rectangular bounds from trailing simple roots

This internal module makes the local rectangular support implication
quantitative. For `R ≥ 1`, it defines
`rectangularSupportRadius d R = R^(d*(d+1))`.

First, a tuple of `n+1` field units with final norm at most one and
all adjacent ratios of norm at most `R` has every entry of norm at most
`R^n`. Reverse induction proves the sharper intermediate bound
`R^(n-i)` at position `i`, multiplying each ratio by the next entry.
Applied to the final `d+1` entries of an invertible upper triangular
matrix, this bounds their product by `R^(d*(d+1))`.

For the actual three-block chart, the final standard basis row
identifies the last diagonal entry with an entry of the inverse right
factor. Suppose the chart, after reassociation, is `B*K`; `B` is upper
triangular; every entry of `K` and `K⁻¹` has norm at most one; and the
last `d` adjacent ratios of `B` have norm at most `R`. Then every
rectangular entry has norm at most
`R^(d*(d+1)) * (d+1)!`. The proof applies the preceding product bound to
`norm_lowerBlockPair_coordinate_le` from `RectangularIwasawaBounds`.

For an ultrametric norm the factorial is unnecessary. Mathlib's
`NormedField.valuation`, the valuation given by the nonnegative norm,
allows direct reuse of the constant-one determinant bound. The final
ultrametric theorem therefore gives `‖x i j‖ ≤ R^(d*(d+1))`. At `R=1`
this is exactly the unit-ball support implication needed outside a
finite set of places.

These results work over arbitrary normed fields under the stated
entry and factorization bounds, with an extra ultrametric hypothesis
for the constant-one conclusion. They do not construct the
factorization or establish a global Schwartz estimate. No assertion
of Mellin convergence is made.
