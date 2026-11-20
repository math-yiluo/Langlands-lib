# Inverse Mellin transforms of functions decaying in vertical strips

Helper module of an intermediate result of Task 7400, towards
`Langlands.Global.RankinSelbergGlobal.RealPlaceFunctionalEquationStatement`. Authored by
Worker 823. Every declaration is proved, with no axioms beyond Lean's standard ones. The
module imports `ArchimedeanMellinPair` (for `RapidDecay`) and Mathlib.

Notation. Mathlib's Mellin transform is `mellin f s = ∫₀^∞ t^(s-1) f(t) dt`. Its inverse
Mellin transform on the line `Re s = σ` is
`mellinInv σ m t = (1 / 2π) ∫_ℝ t^(-(σ + y i)) m(σ + y i) dy`.

## Main result

`exists_mellin_eq`: let `m : ℂ → ℂ` be entire and satisfy `StripDecay m`. Then there is
`h : ℝ → ℂ` with:
- `h` measurable;
- `RapidDecay h`: for every real `M` there is `C` with `‖h t‖ ≤ C t^M` for all `t > 0`;
- `mellin h s = m s` for every `s : ℂ`.

The function is `h = mellinInv 0 m`.

`StripDecay m` means: for all reals `a, b` there is `C` such that
`‖m(x + y i)‖ ≤ C (1 + y²)⁻¹` whenever `a ≤ x ≤ b` and `y` is real.

## Declarations

All in the namespace `Langlands.Global.RankinSelbergGlobal.ArchimedeanInverseMellin`.

- `StripDecay`: the definition above.
- `integrable_vertical`: a continuous `f` with `‖f(x + y i)‖ ≤ C (1 + y²)⁻¹` is integrable on
  the vertical line `Re s = x`. It is dominated by Mathlib's `integrable_inv_one_add_sq`.
- `tendsto_inv_one_add_sq`: `(1 + T²)⁻¹ → 0` as `T → ∞`.
- `integral_vertical_eq` (contour shift): let `f` be entire with
  `‖f(x + y i)‖ ≤ C (1 + y²)⁻¹` for `a ≤ x ≤ b`. Then `∫ f(a + y i) dy = ∫ f(b + y i) dy`.
  - Mathlib's `integral_boundary_rect_eq_zero_of_differentiableOn` on the rectangle
    `[a, b] × [-T, T]` shows that `i` times the difference of the vertical integrals over
    `[-T, T]` equals the difference of the two horizontal integrals.
  - Each horizontal integral has norm at most `C (1 + T²)⁻¹ |b - a|`, so it tends to `0`.
  - The vertical integrals tend to the full integrals (`intervalIntegral_tendsto_integral`).
  - Uniqueness of limits gives the claim.
- `norm_ofReal_cpow_neg`: `‖t^(-(x + y i))‖ = t^(-x)` for `t > 0`.
- `rpow_neg_le_add`: `t^(-x) ≤ t^(-a) + t^(-b)` for `t > 0` and `a ≤ x ≤ b`.
- `mellinInv_eq_of_stripDecay`: for `m` entire with `StripDecay m` and `t > 0`,
  `mellinInv a m t = mellinInv b m t` for all `a, b`. This is `integral_vertical_eq` applied
  to `s ↦ t^(-s) m(s)`, which satisfies the strip bound with constant `C (t^(-a) + t^(-b))`.
- `norm_mellinInv_le`: `‖mellinInv c m t‖ ≤ (1 / 2π) (∫ ‖m(c + y i)‖ dy) t^(-c)` for `t > 0`.
- `measurable_mellinInv`: `mellinInv c m` is measurable for continuous `m`. It is a parametric
  integral of a jointly measurable function (`StronglyMeasurable.integral_prod_right`).
- `rapidDecay_mellinInv`: `RapidDecay (mellinInv 0 m)`. Given `M`, replace the line
  `Re s = 0` by `Re s = -M` (`mellinInv_eq_of_stripDecay`). Then `norm_mellinInv_le` gives
  `‖mellinInv 0 m t‖ ≤ C t^M`.
- `exp_neg_abs_le`: `exp(-|u|) ≤ 2 (1 + u²)⁻¹`, from `1 + v + v²/2 ≤ exp v` for `v ≥ 0`.
- `mellin_mellinInv`: `mellin (mellinInv 0 m) s = m s` for all `s`. Write `c = Re s` and
  `g(y) = m(c + 2π y i)`.
  - By Mathlib's `mellin_eq_fourier`, `mellin h s = 𝓕 G (Im s / 2π)` with
    `G(u) = e^(-c u) h(e^(-u))`.
  - Move the line to `Re s = c` (`mellinInv_eq_of_stripDecay`). Then Mathlib's
    `mellinInv_eq_fourierInv` shows `G = 𝓕⁻ g`.
  - `g` is integrable by the strip bound on `[c, c]`.
  - `G` is integrable: rapid decay of `h` with exponents `1 - c` and `-1 - c` gives
    `‖G(u)‖ ≤ (|C₁| + |C₂|) e^(-|u|)`, and `exp_neg_abs_le` turns this into a bound by
    `(1 + u²)⁻¹`. Hence `𝓕 g = G(-·)` is integrable (`Real.fourierInv_eq_fourier_neg`).
  - Fourier inversion (`Integrable.fourier_fourierInv_eq`) gives
    `mellin h s = g(Im s / 2π) = m(c + Im s · i) = m(s)`.
- `exists_mellin_eq`: the main result, with `h = mellinInv 0 m`.

## Relation to the literature

Jacquet, *Archimedean Rankin–Selberg integrals* (2009), §4.1, p. 22, states the converse
direction of the Mellin correspondence on `S(ℝ^×_+)`. Let `m(s)` be entire such that `P(s) m(s)`
is bounded at infinity in vertical strips for every polynomial `P`. Then
`φ(t) = (1 / 2iπ) ∫_(a - i∞)^(a + i∞) m(s) t^(-s) ds` lies in `S(ℝ^×_+)` and `Mφ(s) = m(s)`.
With `s = a + y i` this `φ` is Mathlib's `mellinInv a m`. The present module proves a variant:
- the hypothesis is only decay like `(1 + y²)⁻¹` in each vertical strip;
- the conclusion is measurability and rapid decay of `φ` together with `Mφ = m`;
- smoothness of `φ` and membership in `S(ℝ^×_+)` are not proved.

The proof is the standard one: a contour shift gives the size bounds, and Fourier inversion
along a vertical line gives `Mφ = m`.
