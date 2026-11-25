# The identity theorem on a totally real slice

Module `Langlands.Analysis.SeveralComplex.RealSliceIdentity` (namespace
`Langlands.Analysis.SeveralComplex`). Helper of
`Langlands.Analysis.SeveralComplex.RealHyperplaneDivision` (for Lapid
2011 Proposition 6). Provenance: internal; standard complex analysis proved
from Mathlib's one-variable identity theorem.

## Declarations

- `realSlice s₀ x : Fin n → ℂ` is the point `s₀ + i x`, coordinatewise
  `s₀ j + Complex.I * (x j : ℂ)`, for `x : Fin n → ℝ`. `realSlice_apply` is its
  defining equation.
- `norm_realSlice_sub`: `‖realSlice s₀ x - s₀‖ = ‖x‖` (sup norms), and
  `dist_realSlice`: `dist (realSlice s₀ x) s₀ = ‖x‖`.
- `eqOn_zero_of_realSlice`: if `G : (Fin n → ℂ) → ℂ` is complex
  differentiable on the polydisc `ball s₀ r` (the sup-norm ball) and
  `G (realSlice s₀ x) = 0` for every real `x` with `‖x‖ < δ`, where `δ > 0`, then
  `G = 0` on `ball s₀ r`.

## Proof of `eqOn_zero_of_realSlice`

Let `δ' = min δ r`. By induction on `k` one shows: `G s = 0` for every
`s ∈ ball s₀ r` whose coordinates of index `≥ k` have the form
`s₀ j + i t` with `|t| < δ'`. For `k = 0` such an `s` is `realSlice s₀ t`
with `‖t‖ < δ`. For the step from `k` to `k + 1` (with `k < n`) fix such an
`s` for `k + 1` and consider `φ(z) = G (update s k z)` on the disc
`ball (s₀ k) r`. It is holomorphic (composition with
`Function.update`, `hasFDerivAt_update`), and by the case `k` it vanishes at
the points `s₀ k + i t`, `|t| < δ'`, which accumulate at `s₀ k`. The
one-variable identity theorem
(`AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero`, with
`DifferentiableOn.analyticOnNhd`) gives `φ = 0` on the disc, in particular
at `s k`. For `k = n` the condition on the coordinates is empty.
