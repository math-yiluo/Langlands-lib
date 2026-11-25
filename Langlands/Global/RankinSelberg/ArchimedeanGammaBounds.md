# Exponential type in vertical strips and Gamma factors

Helper module of an intermediate result towards
`Langlands.Global.RankinSelbergGlobal.RealPlaceFunctionalEquationStatement`. Every declaration is proved, with no axioms beyond Lean's standard ones. The
module imports `ArchimedeanInverseMellin` and Mathlib's Gamma-function files.

It shows that `1/Γ`, `1/Γ_ℝ` and `1/Γ_ℂ` have exponential type in vertical strips. It also
shows that multiplying such a function by `exp(s²)` gives the decay `StripDecay` of
`ArchimedeanInverseMellin`. Here `Γ_ℝ(s) = π^(-s/2) Γ(s/2)` and `Γ_ℂ(s) = 2 (2π)^(-s) Γ(s)`
are Mathlib's `Complex.Gammaℝ` and `Complex.Gammaℂ`.

## Declarations

All in the namespace `Langlands.Global.RankinSelbergGlobal.ArchimedeanInverseMellin`.

`StripExpType f` means: for all reals `a, b` there are `C ≥ 0` and `K ≥ 0` with
`‖f(x + y i)‖ ≤ C exp(K |y|)` whenever `a ≤ x ≤ b` and `y` is real.

Closure properties, in the namespace `StripExpType`:
- `congr`: invariance under pointwise equality.
- `mul`: products. The constants multiply and the exponents add.
- `const`: constant functions.
- `comp_add`: `s ↦ f(s + w)` for complex `w`. The strip is shifted by `Re w`, and `C` is
  multiplied by `exp(K |Im w|)`.
- `comp_ofReal_mul`: `s ↦ f(r s)` for real `r`. It uses the strip `|Re s| ≤ |r| (|a| + |b|)`
  and the exponent `K |r|`.
- `ofReal_cpow`: `s ↦ r^s` for real `r > 0`, with `‖r^s‖ = r^(Re s) ≤ r^a + r^b`.
- `list_prod`: products over a list of functions of exponential type.

The Gamma function:
- `rpow_le_add`: `t^x ≤ t^a + t^b` for `t > 0` and `a ≤ x ≤ b`.
- `bounded_on_rect`: a continuous function is bounded on each rectangle `a ≤ Re s ≤ b`,
  `|Im s| ≤ 1`. The rectangle is compact.
- `norm_sin_le`: `‖sin z‖ ≤ exp |Im z|`, from `2 sin z = (e^(-iz) - e^(iz)) i`.
- `norm_Gamma_le`: `‖Γ(z)‖ ≤ Γ(p) + Γ(q)` for `0 < p ≤ Re z ≤ q`. It bounds Euler's integral
  using `t^(Re z - 1) ≤ t^(p-1) + t^(q-1)`.
- `inv_Gamma_eq_of_re_lt_one`: `Γ(s)⁻¹ = Γ(1 - s) sin(π s) / π` for `Re s < 1`. This is the
  reflection formula `Complex.Gamma_mul_Gamma_one_sub`. When `sin(π s) = 0`, `s` is an integer
  `≤ 0`, so both sides vanish: Mathlib's `Γ` is `0` at its poles.
- `inv_Gamma_bound_left`: for `b < 1`, `‖Γ(x + y i)⁻¹‖ ≤ C exp(π |y|)` on `a ≤ x ≤ b`. This
  combines the two previous estimates.
- `inv_Gamma_bound_shift`: a bound `C exp(π |y|)` on the strip `[a, b]` gives one on
  `[a + 1, b + 1]`.
  - For `|y| ≥ 1`, use `Γ(s) = (s - 1) Γ(s - 1)` and `‖(s - 1)⁻¹‖ ≤ 1`.
  - For `|y| ≤ 1`, use `bounded_on_rect` for the entire function `1/Γ`.
- `inv_Gamma_stripExpType`: `StripExpType (fun s => Γ(s)⁻¹)`, with exponent `π`. The proof is
  by induction on the number of unit shifts needed to reach `Re s < 1`.
- `inv_Gammaℝ_stripExpType`: since `Γ_ℝ(s)⁻¹ = π^(s/2) Γ(s/2)⁻¹`, it follows from
  `ofReal_cpow`, `comp_ofReal_mul (1/2)` and `mul`.
- `inv_Gammaℂ_stripExpType`: likewise, from `Γ_ℂ(s)⁻¹ = 2⁻¹ (2π)^s Γ(s)⁻¹`.
- `stripDecay_exp_sq_mul`: if `StripExpType f`, then `StripDecay (fun s => exp(s²) f(s))`. On
  `a ≤ x ≤ b`, `|exp((x + y i)²)| = exp(x² - y²)` and `x² ≤ a² + b²`. With `K |y| ≤ y²/2 + K²/2`
  this gives `exp(x² - y²) C exp(K |y|) ≤ C exp(a² + b² + K²/2) exp(-y²/2)`. Finally
  `1 + y² ≤ 2 exp(y²/2)`.
- `StripDecay.comp_add_ofReal`: `StripDecay` is preserved by real shifts `s ↦ f(s + c)`.
- `StripDecay.congr`: invariance under pointwise equality.

## Relation to the literature

Jacquet, *Archimedean Rankin–Selberg integrals* (2009), p. 22–23, uses two facts to construct
`(σ, ψ)` pairs:
- in a vertical strip the reciprocals of the `L`-factors are bounded by `e^(D|y|)`;
- `e^(P(s))` with `P(s) = A s² + B s + C`, `A > 0`, is bounded by `e^(-C y²)`, `C > 0`.

This module proves the first fact for `1/Γ`, `1/Γ_ℝ` and `1/Γ_ℂ`, and the resulting decay for
`P(s) = s²` in the form used by `ArchimedeanInverseMellin`. The proofs (reflection formula,
Euler's integral, functional equation `Γ(s + 1) = s Γ(s)`) are standard; no Stirling-type
asymptotics are used, and the exponent obtained for `1/Γ` is `π`.
