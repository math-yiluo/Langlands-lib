# The core of the adjacent-rank step

Internal helper for the proof of `HighlyRamifiedGammaStabilityStatement`. This is the main
argument of Jacquet–Shalika 1985, §4.4 (printed pages 327–331), in Library conventions. The
candidates have rank `m + 3` and the test has rank `m + 2`, so the auxiliary representations
`τ` have rank `m + 1`. The canonical structures are local instances.

- `model_scalar_mul`: a model function of a representation with central character `ω` satisfies
  `w(z g) = ω(z) w(g)` for scalars `z` (`model_mul_scalar`, TestSide, and the commutation of
  scalars).

## Statement

`core_gamma_eq` assumes:
- the completeness lemma `WhittakerCompletenessStatement` (Jacquet–Shalika 1985, Lemma (3.2));
- an additive character `ψ` of conductor exponent `0` and an additive Haar measure `ν`;
- levels `f, b ≥ 1` and `c` with `c ≥ f + b` and `c ≥ 2f` (conditions (8) and (4.4.21));
- generic candidates `π₁, π₂` of rank `m + 3` with a common central character `ω` trivial on
  `1 + 𝔭^f`, nonzero functionals, and model vectors `w₁, w₂` fixed by `K_1(f)`, equal on the
  mirabolic subgroup, with `w_i(1) = 1` (the output of `EssentialPairInput`);
- a generic test `σ` of rank `m + 2`, a character `ω_σ` trivial on `1 + 𝔭^b`, a nonzero
  `ψ⁻¹`-functional `ℓ'`, a quasicharacter `χ` trivial on `1 + 𝔭^b`, and `ϖ` of order `1`;
- the Kirillov shell vector `f'` of `σ` (`hsupp`, `hval` with `κ₁ ≠ 0`, `hequiv` with the
  character `ω_σ χ^(m+1)`). It is an internal replacement for the vector `W'` of JS85
  (4.4.16)–(4.4.17), not that vector (see `KirillovShell.md`, Provenance);
- monomial gamma factors (`hGall`): for every generic `τ` of rank `m + 1` with a level-`f` vector
  and central character `ω_τ` there is a certificate of `(σ^ι ⊗ χ⁻¹ ∘ det, τ)` equal to
  `C(ω_τ) X^(c(m+1))`. JS85 (4.4.15) states the monomial form for `(σ ⊗ χ) × τ`. This
  project uses the pair `(σ^ι ⊗ χ⁻¹ ∘ det, τ)` instead, and `MonomialTwistGamma` applied to
  `σ^ι` supplies it.

The conclusion: two gamma certificates of `(π₁ ⊗ χ ∘ det, σ)` and `(π₂ ⊗ χ ∘ det, σ)` are equal.

## Proof

1. Test data. `T₂` is a set of representatives of `ϖ^(-c) O^(m+1)` modulo `O^(m+1)`
   (`exists_finset_addCosetReps`), and `Φ₂ = dualWeight` (JS85 (4.4.18)).
   `S₁ = (ω_σ χ^(m+2)) 1_(O^×)` is periodic modulo `𝔭^b` (`unitCharWeight_add`), so
   `exists_unit_inversion` gives `T₁ ⊆ ϖ^(-b) O` and `Φ₁` with `Σ Φ₁(u) ψ(u ξ) = S₁(ξ)` on `O`
   (condition (6)). `T = T₁ × T₂` and `Φ = Φ₁ ⊗ Φ₂`.
2. Candidate test vectors `F_i` (`exists_candidateTest_model`). The `I`-side: every point of
   `T` with `Φ ≠ 0` is a deep first row (`productTest_isDeepFirstRow`, using `c ≥ f + b`).
   `testValue_eq_at_weyl` (ISide) then gives `F₁(diag(g,1)) = F₂(diag(g,1))` for all `g`, so the
   two forward corank-one integrals are equal for every `s`.
3. The smeared function. `exists_twistedSmear_model` (TwistedSmearModel) gives a model vector
   `U` of `Π = σ^ι ⊗ χ⁻¹ ∘ det` equal to `twistedSmear`. Its weight is locally constant and
   compactly supported (CoreAnalytic).
4. The `F`-side. `shell_discharge` (ShellDischarge) with `ω₀ = ω⁻¹` gives the shell identities
   for all `ψ⁻¹`-generic representations, with the constant `c₀ = shellConstant(ω⁻¹)`.
   `rightAverage_eq_target_of_shells` (CompletenessStep) then gives
   `avg(F_A) = c₀ t` for `F_A = corankRestriction U`. Smoothness, unipotent equivariance and
   shell-wise compact support of `F_A` come from CoreAnalytic.
5. The `J`-side. `dual_integral_value` (CoreJSide) applies to both candidates with the same
   `C'`, `U` and `c₀`. Its inputs are: `S₂ = integralFourier` with support in `(𝔭^f)^(m+1)`
   (`c ≥ 2f`); `η = (ω_σ χ^(m+1))⁻¹` from `hequiv` (`secondDual_lowerBlockPair`); the
   last-coordinate weight (`lastWeight_unitCharWeight`); the relation between `U` and `f̃'`
   (`integral_integralFourier_eq`); and measurability and integrability for `Re s` large
   (`dual_integrand_measurable_integrable`). Both dual integrals equal
   `C' χ(det w) c₀ · 1 ≠ 0` (`shellConstant_ne_zero`, `w_i(1) = 1`).
6. `gamma_eq_of_adjacent_tests` (AdjacentComparison) concludes `G₁ = G₂`.
