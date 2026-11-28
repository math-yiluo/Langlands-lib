# The limiting weight on `O(n)` and its nonzero integral

Module `Langlands.Global.RankinSelberg.RealCompactDiracWeight`, namespace
`Langlands.Global.RankinSelbergGlobal.RealCompactDirac`.

Notation as in `RealCompactDiracSeed`: `Δₗ = corner κ l` (`Δₙ = 1`), `Q = cornerProduct κ`,
`P = signPart p κ`, for `κ ∈ O(n)`; `s : Fin n → ℂ`, `q = growthExponent s = ∑ₗ |Re s_l|`.
The measure is the Haar probability measure `haarOrthogonal n`.

## Definitions

* `cornerRatio X l = |Δₗ(X) / Δₗ₊₁(X)|` and `ratioProduct s X = ∏_{l < n} cornerRatio X l ^ s_l`
  (complex powers of nonnegative reals).
* `weight p m s κ = |P(κ)| Q(κ)^{2m} · ratioProduct s κ`.
* `signDegree n p = 2 ∑_{l < n} p l`, `exponentNorm s = ∑ₗ ‖s_l‖`, and
  `laplaceThreshold s = exp(-1/(4 exponentNorm s + 4)) ∈ (0, 1)`.

## Bounds on `O(n)`

* `abs_corner_orthogonal_le_one`, `abs_cornerProduct_le_one`, `abs_signPart_le_one`: corner
  minors of orthogonal matrices have absolute value at most `1` (`abs_corner_le_one`), hence so
  do `Q` and `P`.
* `abs_cornerProduct_le_corner`: `|Q| ≤ |Δⱼ|` for every `j`.
* `abs_signPart_ge`: `|Q|^{signDegree n p} ≤ |P|`.
* `cornerRatio_bounds`, `cornerRatio_pos`: if `Q ≠ 0`, every ratio lies in `[|Q|, |Q|⁻¹]`.
* `norm_ratioProduct_le`: if `Q ≠ 0`, `‖ratioProduct s κ‖ ≤ (|Q|⁻¹)^q` (each factor has norm
  `ratio^{Re s_l} ≤ (|Q|⁻¹)^{|Re s_l|}` by `rpow_le_of_le_of_inv_le`).
* `weight_of_cornerProduct_eq_zero`, `norm_weight_le`: for `m ≥ 1`, `W = 0` where `Q = 0`, and
  `‖W(κ)‖ ≤ |Q|^{2m} (|Q|⁻¹)^q` everywhere.
* `pow_mul_inv_rpow_le_one`, `norm_weight_le_one`: if `q ≤ 2m` then `‖W‖ ≤ 1`.
* `measurable_weight`, `integrable_weight`: `W` is measurable and, for `q ≤ 2m`, integrable.

## The Laplace argument

* `re_ratioProduct_ge`: if `|Q(κ)| > laplaceThreshold s`, then `Re ratioProduct s κ ≥ 1/2`.
  Write `ratioProduct s κ = exp z` with `z = ∑ₗ log(cornerRatio κ l) s_l`. Since every ratio lies
  in `[|Q|, |Q|⁻¹]`, `|log ratio| ≤ -log |Q| < 1/(4 exponentNorm s + 4)`, so `‖z‖ ≤ 1/4`, and
  `‖exp z - 1‖ ≤ 2 ‖z‖ ≤ 1/2` (Mathlib's `Complex.norm_exp_sub_one_le`).
* `exists_re_integral_weight_pos` (**nonvanishing of `∫ W`**): there is `M₀` such that
  `Re ∫_{O(n)} W dk > 0` for every `m ≥ M₀`.

Proof of `exists_re_integral_weight_pos`. Let `Q₀ = laplaceThreshold s`,
`Q₁ = (1 + Q₀)/2 ∈ (Q₀, 1)` and `A₁ = {κ : |Q(κ)| > Q₁}`. `A₁` is open and contains `1`
(`Q(1) = 1`), so `μ(A₁) > 0` (Haar measures charge open sets). With `d = signDegree n p`, choose
`M₀ ≥ max(1, q)` such that `((Q₀/Q₁)²)^m < ½ Q₁^d Q₀^q μ(A₁)` for every `m ≥ M₀`. Pointwise,
`Re W ≥ c₁ 1_{A₁} - c₂` with `c₁ = ½ Q₁^{d + 2m}` and `c₂ = Q₀^{2m} (Q₀⁻¹)^q`:

* where `Q = 0`, `W = 0`;
* where `0 < |Q| ≤ Q₀`, `Re W ≥ -‖W‖ ≥ -|Q|^{2m - q} ≥ -Q₀^{2m - q} = -c₂`;
* where `|Q| > Q₀`, `Re W = |P| Q^{2m} Re(ratioProduct) ≥ ½ |P| Q^{2m} ≥ 0`, and on `A₁` this is
  at least `½ |Q|^{d + 2m} ≥ c₁` by `abs_signPart_ge`.

Integrating (`integral_mono`, `integral_re`), `Re ∫ W ≥ c₁ μ(A₁) - c₂ > 0`, since the choice
of `M₀` gives `c₂ < c₁ μ(A₁)`.

## Provenance

Derived, internal; no literature source is claimed. The weight enters the compact pairing
through `exists_pointwise_error` (module `RealCompactDiracBigCell`), whose hypotheses are:
characters with `χ_l(1) = 1` and `χ_l(-1) = (-1)^{p l}` for the parity data `p`, `m ≥ 1` and
`2m ≥ 1 + (n + 2) q` with `q = growthExponent s`, a continuous test `ψ` on `O(n)` that is
`IsSignCovariant χ ψ` (inverse-sign covariant for these characters) with a Lipschitz constant
`L ≥ 0` for the row-sum matrix norm, and `t ≥ 1`. Under these hypotheses the transferred
integrand `seedProfile p m κ · Ψ(κ a_t⁻¹)` divided by `scaleFactor s t` differs from
`weight p m s κ · ψ(1)` by at most `t⁻¹ (‖ψ‖ + L) K` uniformly on `O(n)`, with `K` independent
of `ψ`, `L`, `κ` and `t`. In the proof of `RealStandardCompactDiracStatement`, `m` is chosen so
large that also
`Re I > 0` for `I = ∫ W` (`exists_re_integral_weight_pos`), and the integral of the transferred
integrand is finally divided by `scaleFactor s t · I`. The nonvanishing replaces the remark of
Bernstein–Krötz, *Smooth Fréchet globalizations of Harish-Chandra modules*, arXiv:0812.1684v3,
p. 59, that the normalizing integral of their seed is nonzero once its exponent is large.
