# Kernels of the four-crossing induced-pair operator

This internal supporting unit analyzes the actual operators defined in
`RealInducedPairFrobenius`. It derives its assertions from their compact Fourier
identities, the two proved landing routes, and the adjacent-window injectivity
criterion in `RealAdjacentMultiplierInjectivity`. No external literature assertion
is used. The principal namespace is
`Langlands.Archimedean.RealInducedPairKernelRecovery`.

Write `L = |d.weight|`, `M = |e.weight|` and let
`h : RealInducedPairFrobenius.MultiplierData d e δ μ₁ μ₀ μ₂ μ₃`.
All assertions retain these supplied recurrent symmetric multiplier data. The
parameter `δ` is arbitrary. There is no exponent-order assumption.

For general Frobenius data, `blockFrobMap_eq_zero_iff` describes its kernel:
the source Fourier coefficients vanish at every compact point and every mode
where the multiplier is nonzero. The forward implication uses the multiplier
identity and cancellation. The reverse implication sets all target coefficients
to zero and applies compact Fourier uniqueness in the target standard module.

For a natural cutoff `ℓ` satisfying `Even (ℓ - 1 - ε)`, suppose that on the
parity class `Even (j - ε)` the multiplier is nonzero exactly when `ℓ < |j|`.
Then `blockFrobMap_eq_zero_iff_tail` says its kernel consists exactly of source
vectors whose coefficients vanish for `ℓ ≤ |j|` at every compact point.
The equality case is absent from the source parity class, by `abs_ne_cutoff`.
Coefficients off the parity class vanish by the source sign relation. This
result does not assume that a particular tail multiplier has been chosen.

`firstMultiplier` restricts the first full-character crossing to the actual
source `[induced d, induced e]`. Its multiplier is `μ₁` at position one.
`to1_injective_of_cutoff` proves this crossing injective when `μ₁` is nonzero
on its parity class for `m ≤ |j|`, and either `m < L` or `m < M`.
The first alternative uses the source induction window at position zero;
the second uses the window at position two. Both apply the existing adjacent
uncertainty criterion. `to1_eq_zero_iff_tail` retains both source induction
constraints in the exact tail-kernel description, and `to1_injective_of_tail`
specializes the criterion to that description.

The two middle orders give more information. The proved landing memberships
put `h.to10 f` in `[first e, induced d, second e]` and `h.to12 f` in
`[first d, induced e, second d]`. Forgetting each recovered induction constraint
includes these spaces in their respective full-character spaces.
`rightMultiplier` and `leftMultiplier` restrict the next crossing to these
recovered-window spaces.

`to3_eq_zero_iff_to10` and `ker_to3_eq_ker_to10` assume a natural `m < L`
and `μ₂ j ≠ 0` whenever `Even (j - 0)` and `m ≤ |j|`. They prove that the
three-crossing kernel equals the first-two-crossing kernel in the induced-first
order. Indeed, the recovered `d` window is at position one, adjacent to the
right crossing at position two. The supplied cutoff makes that crossing
injective on the entire recovered-window module.

`to3_eq_zero_iff_to12` and `ker_to3_eq_ker_to12` use the alternative order.
Their assumptions are `m < M` and `μ₀ j ≠ 0` whenever
`Even (j - (L + M + 2))` and `m ≤ |j|`. The recovered `e` window at position
one makes the left crossing at position zero injective. The disjoint-crossing
identity `h.to3_eq` identifies its output with the same three-crossing map.
If both sets of assumptions hold, all three displayed kernels are equal.

The selected Prop definition `RealInducedPairKernelRecoveryStatement` universally
quantifies `d`, `e`, `δ`, all four multipliers and `h`, and asserts these two
conditional equalities of kernels. `realInducedPairKernelRecovery` proves it
using the preceding lemmas.

These are kernel descriptions and conditional recovery results. The unit does
not construct the multiplier data, identify nonzero kernels with images of
heavier standard modules, analyze the final crossing, or establish the
unconditional `RealInducedInducedFiltrationStatement`.
