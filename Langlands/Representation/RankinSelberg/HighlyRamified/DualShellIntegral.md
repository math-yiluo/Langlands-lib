# The dual integral of the Kirillov test vector

Internal helper for the proof of `HighlyRamifiedGammaStabilityStatement` (Jacquet–Shalika 1985,
§4.4, printed page 330: with the choices (16)–(18), the right-hand side of (14) reduces to the
right-hand side of (13)). Here the internal Kirillov shell vector (`KirillovShellInput`)
replaces their `W'` of (16)–(17), and the restriction to `K⁰(f)` comes from the weight (18)
(step 4 of `dual_shell_integral` below). The canonical topology, valuation and Borel structures are local
instances; `abv` is the published `normalizedAbsoluteValue` and the quotient measure is the
published `unipotentQuotientHaar`.

## Matrix lemmas

- `scalar_commute`, `inverseTranspose_scalar` (`ᵗ(u I)⁻¹ = u⁻¹ I`), `determinant_scalar`
  (`det(u I) = u^(m+1)`).
- `weylLong_inverseTranspose_last`: the last row of `w ᵗk⁻¹` is the first column of `k⁻¹`.
  `weylLong_inverseTranspose_involutive`: `k ↦ w ᵗk⁻¹` is an involution.
- `isIntegralMatrix_iff_mem_level`: `GL_(m+1)(O)` is the published level-zero subgroup
  `Conductor.levelOpenSubgroup F m 0`. `isIntegralMatrix_weylLong`,
  `isIntegralMatrix_inverseTranspose`, `isIntegralMatrix_weylLong_inverseTranspose_iff`:
  `k ↦ w ᵗk⁻¹` preserves `GL_(m+1)(O)`.
- `abv_eq_one_of_valuation`: the normalized absolute value is `1` on valuation units.
- `inFirstColumn_isIntegralMatrix`: `K⁰(f) ⊆ GL_(m+1)(O)`.

## The shell evaluation

Fix a unit `ϖ`, `c`, a constant `κ₁` and a constant `ωτ`, and write `z = (ϖ^c)⁻¹ I`.

- `dualShellConstant F η χ ϖ c m κ₁ ωτ s =
  χ(det w)⁻¹ χ(ϖ^(-c))^(m+1) η(O)^(m+1) κ₁ ωτ |det z|^(s-1/2)`.
- `corankOneFunction_dualShell`: suppose `f'(diag(k z, 1)) = κ₁ χ(det k)⁻¹` for `k ∈ GL_(m+1)(O)`,
  `F = twistedSmear …` (as a Whittaker function `Fbig`), and `W''(g ϖ^c) = ωτ W''(g)`. Then
  the published dual corank-one function at `k z`, `k ∈ GL_(m+1)(O)`, is
  `dualShellConstant · φ(-rev k_last) · W''(w ᵗk⁻¹)`, with `φ = unitLastWeight ω f`.
  It combines `twistedSmear_at_dual`, `ϖ^c (k z)_(last, j) = k_(last, j)`, and the right
  invariance of `|det|^s` under `GL_(m+1)(O)` (published
  `Conductor.determinantWeight_mul_integral`).
- `integral_weylLong_inverseTranspose`: `∫ φ(w ᵗg⁻¹) dg = ∫ φ(g) dg` for the published Haar
  measure `generalLinearHaar`. Inverse transpose preserves it (published
  `generalLinearHaar_measurePreserving_inverseTranspose`), and so does left translation.
- `dual_shell_integral`: in addition, assume that `f'(diag(B,1)) ≠ 0` forces
  `u B ϖ^c ∈ GL_(m+1)(O)` for some `u ∈ N`, and that `Fbig` and `W''` are right invariant
  under open subgroups. Then
  `corankOneIntegral (ψ.scale (-1)) abv μ (firstDualFunction Fbig) (secondDualFunction W'') s =
  dualShellConstant · ω(-1)⁻¹ · ∫_(K⁰(f)) ω(k₀₀) W''(k) dk`.
  The integrand on `K⁰(f)` is written `(firstColumnCharacter ω hf k)⁻¹ W''(k)`, and the integral
  is over `generalLinearHaar`.
  Steps:
  1. The quotient integral is the integral of the corank-one function at representatives.
  2. Right translation by the central `z` (right invariance of the compatible quotient
     measure, `integral_out_mul_right`).
  3. The translated function is supported on `N · GL_(m+1)(O)` and continuous: it is right
     invariant under an open subgroup built from the smoothness subgroups of `Fbig` and `W''`.
     Moreover `μ_N(N(O)) = 1` (published `unipotentHaar_integral`). Hence `integral_out_of_support`
     gives a Haar integral over `GL_(m+1)(O)`.
  4. `corankOneFunction_dualShell` on `GL_(m+1)(O)`, the substitution `k = w ᵗk''⁻¹`, and
     `unitLastWeight_firstColumn` evaluate the integrand as
     `dualShellConstant · ω(-1)⁻¹ · 1_(K⁰(f))(k'') ω(k''₀₀) W''(k'')`.
