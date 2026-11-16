# The residual integrals

Module `Langlands.Global.RankinSelberg.EqualAnalyticResidue`, namespace
`Langlands.Global.RankinSelbergGlobal.EqualAnalytic`.

Let `P` be `GL_n(F)`-invariant (`n = r + 1`) with `P(a g) = χ(a) P(g)` for scalar ideles, and
`L = log |det|`. The residual integrands are `resLt F r P t = 1_(L<0) P e^(t L)` and
`resGe F r P t = 1_(L≥0) P e^(t L)`. The constant is
`residueConstant F r P w = C_w = ∫_(D ∩ S) P(g) |det g|^(-w/n) dg` (Bochner integral over the
slab `D ∩ S`).

- `integral_res_fibre`: an integrable invariant function integrates as
  `∫_(D ∩ S) ∫_(D₁) f(ζ(a) g) d^×a dg` (the fibration of `EqualAnalyticCentralFibration`).
- `resLt_zeta_mul`, `resGe_zeta_mul`: on the fibre,
  `f(ζ(a) g) = P(g) e^(t L(g)) χ(a) 1_(log |a| ∈ I_g) e^(n t log |a|)`, with
  `I_g = (-∞, -L(g)/n)` and `[-L(g)/n, ∞)` respectively.
- `inner_char_integral`: if `χ = |·|^w`, the inner integral is a Lebesgue integral in
  `y = log |a|` (`integral_logNorm`). Then `exp_mul_char_integral_Iio` and
  `exp_mul_char_integral_Ici` (Mathlib `integral_exp_mul_complex_Iic`, `…_Ioi`) and
  `exp_combine` evaluate it.
- **`residueLt_eq_of_char`**: `∫ resLt t = C_w / (n t + w)` when `Re(w + n t) > 0`.
- **`residueGe_eq_of_char`**: `∫ resGe t = -C_w / (n t + w)` when `Re(w + n t) < 0`.
- **`residueLt_eq_zero`, `residueGe_eq_zero`**: both vanish if `χ(z₀) ≠ 1` for some `z₀` of norm
  one, by `integral_ideleChar_mul_eq_zero`.

Measurability and invariance: `measurable_resLt`, `measurable_resGe`, `resLt_rational_mul`,
`resGe_rational_mul`.

## Provenance

These integrals produce the term `o(s)` and the residues in Cogdell 2004, §2.3, printed
pp.209–210. There `c Φ(0) |det g|^s/(s + iσ)` appears in `E(g)`, and the residues of `I(s)` are
multiples of `∫ φ φ' |det|^(∓iσ)`. Here `C_w` plays the role of
`∫_(Z_n(𝔸)GL_n(F)\GL_n(𝔸)) φ φ' |det|^(-w/n)`, written on the slab representing the central
quotient. The proofs are internal.
