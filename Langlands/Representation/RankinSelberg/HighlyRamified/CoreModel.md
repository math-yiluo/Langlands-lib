# Model vectors and analytic inputs of the adjacent-rank step

Internal helper for the proof of `HighlyRamifiedGammaStabilityStatement`. The remaining
inputs of `core_gamma_eq` that concern model membership, supports, nonvanishing constants and
convergence.

- `exists_candidateTest_model`: for a model vector `w = ℓ(π(·) v)` of `π` and finite test data
  `T, Φ`, the candidate test function `y ↦ χ(det y) Σ_z Φ(z) w(y w₀ n(z))` (`candidateTest`) is
  a model vector of `π ⊗ χ ∘ det`, for the published twisted functional
  `twistFunctional … ℓ` (same linear form). It is the image under the published
  `twistModelLinearMap` of the model vector of `Σ_z Φ(z) π(w₀ n(z)) v`. Placing `χ` on the
  candidate is an internal adaptation. Jacquet and Shalika keep `W_i` in the model of `π_i`
  and put `χ` on `σ`: their functional equation (4.4.1) is written for `π_i × (σ ⊗ χ)`
  (printed page 327), with `W' ∈ 𝒲(σ ⊗ χ; ψ̄)` (printed page 328).
- `integralFourier_dualWeight_inPow`: under condition (8) of the source (`c ≥ 2f`), the
  restricted Fourier transform `S₂` of `Φ₂ = dualWeight` vanishes unless every coordinate lies in
  `𝔭^f` (`dualWeight_fourier_eq_zero`, TestData).
- `integral_integralFourier_eq`: `∫ S₂(rev x) f̃'([[A,0],[x,1]]) dx = χ(det A) · U(diag(A,1))`,
  where `U = twistedSmear` (DualShell). Use `[[A,0],[x,1]] = diag(A,1) ū_x`
  (`lowerBlockPair_one_eq_mul_lowerRow`) and `det diag(A,1) = det A` (published
  `rankInclusion_det`). `S₂(rev x)` is `dualWeightFourier x` by definition.
- `dualShellConstant_ne_zero`, `shellConstant_ne_zero`: the constants of `dual_shell_integral`
  and of the shell identities (ShellDischarge) are products of character values, positive
  volumes (`vol(O)`, `vol(K⁰(f))`), `κ₁ ≠ 0`, a power of a nonzero absolute value and a power
  of `q`. None of them vanishes.
- `dual_integrand_measurable_integrable`: for model vectors `F_c` of a generic `Π` of rank
  `m + 3` and `f'` of a generic `σ` of rank `m + 2`, the dual corank-one integrand
  `(F̃_c, f̃')` for `ψ⁻¹` is measurable for every `s` and integrable for `Re s` large. The dual
  functions are model vectors of the inverse-transpose representations (published
  `firstDualModelMap`, `secondDualModelMap`), which have Whittaker type for `ψ⁻¹`
  (`isOfWhittakerType_firstDual`, `isOfWhittakerType_secondDual`). Integrability is
  `corankOne_integrable_of_whittakerType` (ShellIdentity, from the published
  `unequalRankAnalytic`). Measurability is `measurable_corankOneIntegrand` (CoreAnalytic),
  applied with the open subgroups from smoothness (`model_rightInvariant`,
  `inverseTransposePullback_isSmooth`).
