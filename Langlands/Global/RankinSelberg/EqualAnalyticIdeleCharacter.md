# Idele class characters on `GL_1(𝔸)`

Module `Langlands.Global.RankinSelberg.EqualAnalyticIdeleCharacter`, namespace
`Langlands.Global.RankinSelbergGlobal.EqualAnalytic`.

For an idele class character `χ` (a continuous homomorphism `IdeleClassGroup → ℂˣ`),
`ideleChar F χ z` is `χ(det z)` for `z ∈ GL_1(𝔸)`. It is the value
`Automorphic.centralIdeleCharacter F χ (ideleOf F z)` used in `EqualIntegrals`.

## Results

- `ideleChar` is multiplicative, continuous and trivial on `F^×` (`ideleChar_mul`,
  `ideleChar_one`, `continuous_ideleChar`, `ideleChar_ideleRational`). It is compatible with
  inverses and products of characters (`ideleChar_inv`, `ideleChar_mul_char`).
- **`ideleChar_dichotomy`**: either `χ(z) = |z|^w` (`detPower F 1 z w`) for some `w : ℂ` and
  all `z`, or there is `z₀` with `|z₀| = 1` and `χ(z₀) ≠ 1`. If no such `z₀` exists, `χ` is
  trivial on norm-one ideles. Then `y ↦ χ(normScale y)` is a continuous exponential, hence
  `exp (w y)` (`exists_eq_cexp_of_continuous`). Writing `z = normScale(log |z|) · z₁` with
  `|z₁| = 1` gives `χ(z) = exp (w log |z|) = |z|^w`.
- **`integral_ideleChar_mul_eq_zero`**: if `|z₀| = 1` and `χ(z₀) ≠ 1`, then
  `∫_(D₁) χ(a) u(log |a|) d^×a = 0` for every `u : ℝ → ℂ`. The integrand is `F^×`-invariant, so
  the central translation `a ↦ z₀ a` (`setIntegral_comp_mul_left`) multiplies the integral by
  `χ(z₀)`.

## Provenance

The dichotomy (`χ` unramified of the form `|·|^w`, or nontrivial on `𝔸^1`) is the case
distinction in Cogdell 2004, §2.3, printed pp.209–210, for the poles of the Eisenstein
series and of `I(s)`. The proofs are internal.
