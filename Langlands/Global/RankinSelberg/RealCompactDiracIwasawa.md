# Lipschitz estimates for the Iwasawa coordinates at the identity

Module `Langlands.Global.RankinSelberg.RealCompactDiracIwasawa`, namespace
`Langlands.Global.RankinSelbergGlobal.RealCompactDirac`.

Every `g ∈ GL_n(ℝ)` factors as `g = b κ̂(g)` with `b` upper triangular with positive diagonal
and `κ̂(g) = PrincipalSeriesExtension.signedOrthogonalPart g ∈ O(n)`. The Library's
`PrincipalSeriesExtension.extension s φ g` is `gramExpression s 1 g · φ(κ̂(g))`. This module
estimates both factors near the identity, for the row-sum operator norm of
`Matrix.Norms.Operator`.

## Norm lemmas

* `abs_entry_le_norm`: `|A i j| ≤ ‖A‖`.
* `norm_le_of_abs_entry_le`: if `|A i j| ≤ c` for all entries, then `‖A‖ ≤ n c`.
* `norm_le_of_abs_entry_le_mul`: if `|A i j| ≤ c |B i j|` for all entries (`c ≥ 0`), then
  `‖A‖ ≤ c ‖B‖`.
* `norm_orthogonal_le`, `norm_one_le`: orthogonal matrices and the identity have norm at most
  `n`.
* `rpow_le_of_le_of_inv_le`: for `x > 0` with `x ≤ M` and `x⁻¹ ≤ M`, `x^r ≤ M^{|r|}`.

## The multiplier

* `multiplier s g = gramExpression s 1 (complexify g)`, so that
  `extension s φ g = multiplier s g · φ(κ̂(g))` (`extension_eq_multiplier`, by definition).
* `multiplier_eq`: if `g = b κ` with `b` upper triangular with nonzero diagonal and `κ`
  orthogonal, `multiplier s g = ∏ₗ |b_ll|^{s_l}` (from the Library's `extension_eq` with the
  constant profile `1`). `multiplier_one`: `multiplier s 1 = 1`.
* `continuous_multiplier`, `contDiffAt_multiplier`: from the Library's
  `contDiffOn_gramExpression` on the open set of invertible matrices.
* `growthExponent s = ∑ₗ |Re s_l|` and `heightBase g = (n + 1) · unitHeight g`, with the
  Library's `unitHeight g = max(1, ‖g‖, ‖g⁻¹‖)`.
* `norm_multiplier_le`: `‖multiplier s g‖ ≤ heightBase g ^ growthExponent s`. Proof: write
  `g = diag(a) u k` (Library `exists_diagonalUnits_mul_upperUnipotent_mul_unitaryCompact`) and
  `b = diag(a) u`. Then `|a_l| = |b_ll| ≤ ‖g kᵀ‖ ≤ n ‖g‖`, and `|a_l|⁻¹` is the `(l, l)` entry of
  `b⁻¹ = u⁻¹ diag(a)⁻¹ = k g⁻¹`, so `|a_l|⁻¹ ≤ n ‖g⁻¹‖`. Then
  `‖∏ₗ |a_l|^{s_l}‖ = ∏ₗ |a_l|^{Re s_l} ≤ ∏ₗ heightBase(g)^{|Re s_l|}`.

## Lipschitz bounds

* `exists_eventually_lipschitz`: a map `Mat → E` that is `C¹` at `1` satisfies
  `‖f y - f 1‖ ≤ K ‖y - 1‖` near `1` (Mathlib's `ContDiffAt.exists_lipschitzOnWith`).
* `contDiffAt_signedOrthogonal_entry`: each entry
  `gramColumn i j y · (√gram i y)⁻¹ · (√gram (i+1) y)⁻¹` of the Library's `signedOrthogonal` is
  `C¹` at `1`, since the Gram determinants are positive there (`gram_one_pos`).
  `signedOrthogonal_one`: `signedOrthogonal 1 = 1`.
* `exists_norm_signedOrthogonalPart_sub_one_le`: there is `C ≥ 0` with
  `‖κ̂(g) - 1‖ ≤ C ‖g - 1‖` for **all** `g ∈ GL_n(ℝ)`. Near `1` the entrywise Lipschitz bounds
  combine through `norm_le_of_abs_entry_le`; if `‖g - 1‖ ≥ ε`, then
  `‖κ̂(g) - 1‖ ≤ ‖κ̂(g)‖ + ‖1‖ ≤ 2n ≤ (2n/ε) ‖g - 1‖`.
* `exists_norm_multiplier_sub_one_le`: there is `C ≥ 0` with
  `‖multiplier s g - 1‖ ≤ C ‖g - 1‖ heightBase(g)^q`, `q = growthExponent s`, for all `g`.
  Near `1` this is the local Lipschitz bound (and `heightBase(g)^q ≥ 1`); if `‖g - 1‖ ≥ ε`,
  then `‖multiplier s g - 1‖ ≤ 2 heightBase(g)^q ≤ (2/ε) ‖g - 1‖ heightBase(g)^q` by
  `norm_multiplier_le`.

## Provenance

Derived, internal infrastructure; no literature source is claimed. The estimates are
first-order bounds for the Iwasawa coordinates at the identity. In the proof of
`RealStandardCompactDiracStatement` they take the place of the mean value estimate (12.3) of
Bernstein–Krötz, *Smooth Fréchet globalizations of Harish-Chandra modules*,
arXiv:0812.1684v3, §12.1.4.
