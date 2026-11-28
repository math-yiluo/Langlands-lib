# The translated dual extension on the big cell

Module `Langlands.Global.RankinSelberg.RealCompactDiracBigCell`, namespace
`Langlands.Global.RankinSelbergGlobal.RealCompactDirac`.

Notation as in `RealCompactDiracWeight`; `Ψ = extension s ψ` for a function `ψ` on `O(n)`.

## Definitions

* `scaleUnits n t i = max(t, 1)^{n - 1 - i}`; for `t ≥ 1`,
  `a_t = Iwasawa.diagonalUnits (scaleUnits n t) = diag(t^{n-1}, …, t, 1)`.
* `scaleFactor s t = ∏ₗ (τₗ⁻¹)^{s_l}`, `τ = scaleUnits n t`.
* `IsSignCovariant χ ψ`: `ψ(diag(sgn d) κ) = (∏ᵢ χᵢ(sgn dᵢ))⁻¹ ψ(κ)` for all `d : Fin n → ℝˣ`
  and `κ ∈ O(n)`.
* `heightConstant n = (n + 1)² n! (1 + n + n · lowerConstant n)^{n+1}`.

## Results

* `norm_inv_le_of_det_eq_one`: if `det g = 1` then `‖g⁻¹‖ ≤ n · n! (1 + ‖g‖)^n`, since
  `g⁻¹ = adj g` and each adjugate entry is a determinant with entries bounded by `1 + ‖g‖`
  (`Matrix.adjugate_apply`, `Matrix.det_le`). `heightBase_le_of_det_eq_one`:
  `heightBase g ≤ (n + 1)((n + 1) n! (1 + ‖g‖)^{n+1})`.
* `scaleUnits_div_le`: `τᵢ / τⱼ = t^{-(i-j)} ≤ t⁻¹` for `j < i` and `t ≥ 1`.
* `bigCell_decomposition`: let `χ_l(1) = 1`, `χ_l(-1) = (-1)^{p l}`, `ψ` sign-covariant,
  `κ ∈ O(n)` with `Q(κ) ≠ 0` and `t ≥ 1`. There is `Y ∈ GL_n(ℝ)` with `det Y = 1`,
  `‖Y - 1‖ ≤ t⁻¹ · n · lowerConstant n / |Q(κ)|` and

  `seedProfile p m κ · Ψ(κ a_t⁻¹) = scaleFactor s t · weight p m s κ · Ψ(Y)`.
* `norm_extension_sub_le`: given Lipschitz bounds `‖κ̂(g) - 1‖ ≤ C_κ ‖g - 1‖` and
  `‖multiplier s g - 1‖ ≤ C_ω ‖g - 1‖ heightBase(g)^q` (module `RealCompactDiracIwasawa`) and a
  test `ψ` with `‖ψ k - ψ l‖ ≤ L ‖k - l‖` (`L ≥ 0`),
  `‖Ψ(Y) - ψ(1)‖ ≤ C_ω ‖Y - 1‖ heightBase(Y)^q ‖ψ‖ + L C_κ ‖Y - 1‖`.
* `exists_pointwise_error`: under the hypotheses `χ_l(1) = 1` and `χ_l(-1) = (-1)^{p l}` on the
  characters, if `m ≥ 1` and `1 + (n + 2) q ≤ 2m`, there is `K ≥ 0` such that
  for every sign-covariant continuous `ψ` with Lipschitz constant `L ≥ 0`, every `κ ∈ O(n)` and
  every `t ≥ 1`,

  `‖seedProfile p m κ · Ψ(κ a_t⁻¹) - scaleFactor s t · weight p m s κ · ψ(1)‖ ≤
  ‖scaleFactor s t‖ · t⁻¹ (‖ψ‖ + L) K`.

## Proof of `bigCell_decomposition`

Since `|Q| ≤ |Δₗ|`, all corner minors of `X = κ` are nonzero, so `X = b L` with `b` upper
triangular and `L` lower unipotent (Library `LowerUnipotentRestriction.exists_upper_mul_lower_of_cornerNonzero`,
through `cornerNonzero_of_corner_ne_zero`), and `b_ll = Δₗ/Δₗ₊₁` (`corner_eq_mul_succ`). Put
`D = diag(τ)`, `Y = D L D⁻¹` and `b' = b D⁻¹`. Then `Y` is lower unipotent with entries
`τᵢ L_ij τⱼ⁻¹`, so `det Y = 1`, `|(Y - 1)_ij| ≤ t⁻¹ |(L - 1)_ij|` and
`‖Y - 1‖ ≤ t⁻¹ ‖L - 1‖ ≤ t⁻¹ n · lowerConstant n / |Q|` (`abs_lower_entry_le`,
`norm_le_of_abs_entry_le_mul`). Moreover `X a_t⁻¹ = b' Y`. Write `Y = b_Y k'` (Library
`exists_diagonalUnits_mul_upperUnipotent_mul_unitaryCompact`); then `X a_t⁻¹ = (b' b_Y) k'`, and the
Library's `extension_eq` for both decompositions gives

`Ψ(X a_t⁻¹) = ∏ₗ |b_ll|^{s_l} · ∏ₗ (τₗ⁻¹)^{s_l} · ∏ₗ |b_Y,ll|^{s_l} · ψ(diag(sgn b') diag(sgn b_Y) k')`,
`Ψ(Y) = ∏ₗ |b_Y,ll|^{s_l} · ψ(diag(sgn b_Y) k')`.

Sign covariance turns `ψ(diag(sgn b') ·)` into `(∏ₗ sgn(b_ll)^{p l})⁻¹ ψ(·)`. Finally
`Δₗ Δₗ₊₁ = b_ll Δₗ₊₁²` gives `signPart p X = (∏ₗ sgn(b_ll)^{p l}) |signPart p X|`, and
`|b_ll| = cornerRatio X l`, so the left side equals `scaleFactor s t · weight p m s κ · Ψ(Y)`.

## Proof of `exists_pointwise_error`

If `Q(κ) = 0`, both terms vanish. Otherwise, with `Y` from `bigCell_decomposition` and
`u = |Q|⁻¹ ≥ 1`, the left side is `‖scaleFactor s t‖ ‖W(κ)‖ ‖Ψ(Y) - ψ(1)‖`. The bounds are
`‖Y - 1‖ ≤ t⁻¹ n lowerConstant(n) u`, `‖Y‖ ≤ n lowerConstant(n) u + n`, hence
`heightBase(Y) ≤ heightConstant(n) u^{n+1}` and
`heightBase(Y)^q ≤ heightConstant(n)^q u^{(n+1)q}`; `‖W(κ)‖ ≤ |Q|^{2m} u^q`
(`norm_weight_le`). Multiplying, `‖W‖ ‖Ψ(Y) - ψ(1)‖` is at most
`t⁻¹ n lowerConstant(n) (C_ω heightConstant(n)^q + C_κ)(‖ψ‖ + L) · |Q|^{2m} u^{1 + (n+2)q}`, and the last
factor is at most `1` because `1 + (n + 2) q ≤ 2m`. So
`K = n · lowerConstant(n) · (C_ω heightConstant(n)^q + C_κ)`.

## Provenance

Derived, internal; no literature source is claimed. In Bernstein–Krötz, *Smooth Fréchet
globalizations of Harish-Chandra modules*, arXiv:0812.1684v3, §12.1.4, the translate acts on the
seed in the noncompact picture on `N̄`; here it is moved to the test function (module
`RealCompactDiracTransfer`), and the conjugation `L ↦ a_t L a_t⁻¹`, which contracts `N̄` to the
identity, is applied to the lower unipotent factor of `κ`.
