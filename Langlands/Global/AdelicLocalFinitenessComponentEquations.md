# Difference equations for constant terms and Harish-Chandra components

Module `Langlands.Global.AdelicLocalFinitenessComponentEquations`.

## Residual forms (namespace `StandardConstantTerm`)

`IsTranslationPolynomialSolution b D φ` is the equation `∑_{k ≤ deg D} D_k φ(b^k g) = 0` for all
`g` (module `AdelicLocalFinitenessStatement`); `residualFun b p φ = φ(b^m ·) + ∑_{q < m} p_q φ(b^q ·)`
(module `AdelicStandardSlabEstimate`).

- `lowerCoefficients D = (q ↦ D_q)` and `reversedLowerCoefficients D = (q ↦ D_{m−q} / D_0)`, for
  `q < m = deg D`: the lower coefficients of `D` and of the normalized reversed polynomial
  `D_0⁻¹ x^m D(x⁻¹)`.
- `residualFun_eq_zero_of_monic`: if `D` is monic of degree `m` and `φ` solves the equation of
  `D` for `b`, then `residualFun b (lowerCoefficients D) φ = 0` (the top coefficient is `1`).
- `residualFun_inv_eq_zero`: if `D_0 ≠ 0` and `φ` solves the equation of `D` for `b`, then
  `residualFun b⁻¹ (reversedLowerCoefficients D) φ = 0`, `m = deg D`. Proof: evaluate the equation at
  `b^{−m} g`, use `b^k b^{−m} = (b⁻¹)^{m−k}`, reverse the order of summation and divide by `D_0`.
  This is the equation of the normalized reversed polynomial `D_0⁻¹ x^m D(x⁻¹)` for `b⁻¹`.

## Constant terms and components (namespace `StandardParabolicFamily`)

For a compatible standard parabolic family `𝓕`, standard indices `Q ≤ P`, a point `a` of the
positive split component `𝔄_P` with image `b ∈ G(𝔸)` and a continuous `G(F)`-invariant `f`:

- `isTranslationPolynomialSolution_constantTerm_of_le`: if `C_P f` solves the equation of `D` for
  `b`, so does `C_Q f`. Proof: `C_Q f = C_Q (C_P f)` (`constantTerm_constantTerm_of_le`). The
  function `φ = C_P f` is invariant under `U_P(𝔸)`, so `φ(u b^k g) = φ(b^k u g)` for `u ∈ U_Q(𝔸)`
  (`IsRadicalInvariant.unnormalizedAction_radical_mul` with the point `a^k ∈ 𝔄_P`). Hence
  `∑_k D_k C_Q φ(b^k g) = ∫ ∑_k D_k φ(b^k (u g)) du = 0`, the exchange of the finite sum and the
  integral being justified by the integrability of the constant-term integrands
  (`hasIntegrableConstantTerm_constantTerm_of_le`).
- `isTranslationPolynomialSolution_hcComponent`: if `C_P f` solves the equation of `D` for `b`
  and the index `S ∩ Δ` of a finset `S` lies below `P`, then the Harish-Chandra component
  `𝓕.hcComponent S f = ∑_{S' ⊆ S} (−1)^{|S ∖ S'|} C_{S' ∩ Δ} f` solves it: every index `S' ∩ Δ`
  lies below `P`, and the equation is linear.

## Provenance

Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer. Math. Soc.
37 (2024), 187–234 (literature id `bernstein-lapid-2024-meromorphic-continuation-eisenstein`):
§7.6, p. 219: for a solution `f` of `Ξ_main(s)` the Harish-Chandra components `f_P^S` satisfy
`D_α(s)(T_{a_α})(f_P^S) ≡ 0` for all `α ∈ Δ₀ ∖ Δ_0^P`; here `b = a_α` for the maximal parabolic `P_α` with Levi index `Δ₀ ∖ {α}`, and
`b = z_j` for `P = G`. §7.7, p. 220: the normalized reversed polynomial `D^− = a_0⁻¹ x^m D(x⁻¹)`
for the shifts `z_i⁻¹` on the negative orthants. The equations here use raw left translation, as
in the system `Ξ_main` of the Library statement; the commutation of constant terms with
split-component shifts is the Library result `IsRadicalInvariant.unnormalizedAction_radical_mul`
(module `AdelicConstantTermSplitComponent`).
