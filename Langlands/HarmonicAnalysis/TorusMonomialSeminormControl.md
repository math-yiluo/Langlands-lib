# Finite derivative controls for weighted monomial pullbacks

This is an internal consequence of the Library's angular derivative constructions in
`TorusMonomialDerivative` and scalar derivative seminorms in
`HarishChandraSchwartz.SmoothTorusTensorTopology`. It strengthens their bounds by
making dependence on the varying smooth scalar function explicit. It is not a
new statement attributed to original literature and introduces no topology.
All declarations are in `Langlands.HarmonicAnalysis.TorusFourier`.

For a finite coordinate type `J` with decidable equality,
`torusDerivativeLists n` recursively enumerates all ordered lists of coordinate
directions of length at most `n`. `mem_torusDerivativeLists` proves inclusion of
every such list. `smoothTorusDerivativeControl n` is the finite supremum of the
existing `smoothTorusSeminorm J l` over this set. Thus its value is nonnegative
and bounds every pointwise ordered derivative of order at most `n`, as proved by
`norm_torusPartialDerivList_le_control`. The control includes the empty list,
including when `J` is empty or `n` is zero. It uses precisely the existing scalar
seminorms, with their existing angle normalization.

`torusPartialDeriv_mul` proves the product rule from the two derivatives along
the coordinate translation curve at zero. `torusPartialDerivList_append` and
the singleton formula record the order of composition. Reverse-list induction
then proves `norm_torusPartialDerivList_mul_le`: if all derivatives up to the
list's length of two smooth functions are bounded by `A` and `B`, and `A` is
nonnegative, the derivative of their product is bounded by
`2^length * A * B`. Each induction step applies the product rule at the last
direction and the triangle inequality. No interchange of derivative directions
is assumed. `norm_torusPartialDerivList_mul_le_control` takes `A` and `B` to be
the finite controls and increases the power of two to `n`.

For an integer matrix `a : J → K → ℤ`, `monomialPartialDerivLinear a k` is the
complex-linear operator `sum j, (a j k : ℂ) • torusPartialDerivLinear j` on the
existing smooth-function subalgebra. Its value is the existing pointwise
`monomialPartialDeriv a k`, and powers give its existing function iterate.
`norm_monomialPartialDeriv_iterate_le` proves by induction that a uniform bound
`M` on all ordered derivatives through order `n` yields the bound
`(sum j, norm (a j k : ℂ))^n * M` on the `n`th monomial directional derivative.
The induction uses linearity, the finite-sum triangle inequality, and the
append formula, without assuming that coordinate derivatives commute.

Finally, for finite `K` with decidable equality, a fixed smooth weight `W`, a
fixed matrix `a`, and an order `n`,
`exists_weighted_monomial_derivative_control` supplies one nonnegative real
constant `C`, independent of the smooth scalar input `f`, translate `y`,
coordinate `k`, and evaluation point `z`. Both the value of
`W(monomial a z * y) * f(monomial a z * y)` and every `n`th pure angular
derivative in a `K` direction are bounded by
`C * smoothTorusDerivativeControl n f`. The proof first bounds every ordered
derivative of `W*f`, then applies the existing iterated monomial chain rule.
Explicitly it uses `C = C₀ * D`, where
`C₀ = 2^n * smoothTorusDerivativeControl n W` and
`D = 1 + sum k, (sum j, norm (a j k : ℂ))^n`.
The factor `D` bounds both one and every directional factor, so the same
constant controls values and derivatives, also for empty coordinate types.

These scalar estimates supply finite derivative dependence for the central
Fourier argument. They assert no group-height decay, Schwartz membership, or
Schwartz-valued packet continuity.
