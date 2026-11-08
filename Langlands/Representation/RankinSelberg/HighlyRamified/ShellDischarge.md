# Discharging the shell identities for all test representations

Internal helper for the proof of `HighlyRamifiedGammaStabilityStatement`. The completeness step
(`rightAverage_eq_target_of_shells`, CompletenessStep) needs one shell identity for every
irreducible generic representation `π` of `GL_(m+1)`, generic for `ψ⁻¹ = ψ.scale (-1)`, and
every model vector `w`. In Jacquet–Shalika 1985, §4.4 (printed pages 329–330) this is the
passage from (14)–(15) to (13) for all `τ`; the uniformity of the constant over `τ` is left
implicit there. This module supplies it. The canonical structures are local instances.

## Auxiliary facts

- `isGeneric_of_scale_neg_one`: genericity for `ψ⁻¹` gives genericity for `ψ`, by the published
  change-of-character equivalence `characterChangeFunctionalEquiv` with `a = -1` and
  `(ψ.scale (-1)).scale (-1) = ψ` (`scale_scale`, `scale_one`).
- `inverseAverage_firstColumn_mul`: the inverse `K⁰(f)`-average `w_avg` of DualAverage satisfies
  `w_avg(g k) = ω(k₀₀)⁻¹ w_avg(g)` for `k ∈ K⁰(f)`. Substitute `k' ↦ k' k` in the Haar integral
  and use `omega_firstEntry_mul`. `inFirstColumn_scalar`, `inverseAverage_scalar`: integral
  unit scalars lie in `K⁰(f)`, so `w_avg(g z) = ω(z)⁻¹ w_avg(g)`.
- `unramified_det_eq_one`, `ord_det_eq_zero_of_integral`, `firstColumnTarget_ord_det`: the
  published unramified character `unramifiedCharacter y` is `1` on determinants of order `0`,
  in particular on `GL_(m+1)(O)` and on the support `N K⁰(f)` of the target.
  `firstColumnVolume_ne_zero`: `vol(K⁰(f)) ≠ 0`.
- `corankRestriction F ψ U g = U(diag(g,1)) |det g|^(-1/2)`.
  `setIntegral_corankOneIntegrand_slice`: the integral over the shell `ord det = j` of the
  published corank-one integrand at `s = 0` equals `∫ (F_A · 1_j)(q.out) W'(q.out)` with
  `F_A = corankRestriction`.
- `scaled_whittaker_unipotent`: a `ψ⁻¹`-Whittaker function transforms by `ψ_N⁻¹`.
- `shellConstant F η χ ω ϖ c f m κ₁ C ω_π`: the constant
  `(ω_π(-1)^(m+1))⁻¹ C(ω_π)⁻¹ dualShellConstant(0) ω(-1)⁻¹ vol(K⁰(f)) q^(c(m+1))`, with
  `dualShellConstant` evaluated at `ωτ = ω_π(ϖ^c)`.

## One test representation

`shell_average_identity`: take the data of `shell_identity` (the Kirillov test vector `f'`, the
twisted smeared vector `Fbig` of a representation `Π` of `GL_(m+2)`, the representatives `T`). Let
`π` be generic for `ψ⁻¹` with central character `ω_π`, `w` a model vector for a functional
`ℓ_π`, and assume that the inverse average `w_avg` is not identically zero. Suppose that, once
`π` has a level-`f` principal vector, there is a certificate
`IsPadicPairGammaFactor F ψ ν Π π G` with `G = C(ω_π) X^(c(m+1))`. Then for every `j`,
`∫ (F_A · 1_j) w_avg = [j = 0] shellConstant(ω_π) ∫ t w`. Proof:
1. `w_avg` is a model vector (`exists_model_inverseAverage`, TestSide). Recast it for the
   inverse-character functional by the published `Padic.scaledStandardCoefficientAsInverse`.
2. It is right invariant under the principal congruence subgroup, so `π` has a level-`f`
   principal vector (`hasPrincipalLevelVector_of_model`).
3. `shell_identity` gives the shell integrals. The minus-one scalar `ζ` of the model equals
   `ω_π(-1)` (`model_mul_scalar` at a point where `w_avg ≠ 0`).
4. `integral_firstColumn_inverseAverage` converts `∫_(K⁰(f)) ω(k₀₀) w_avg` into
   `vol(K⁰(f)) ∫ t w`.

## All test representations

`shell_discharge`: let `ω₀` be any character equal to `ω⁻¹` on the integral units, and assume
that the monomial gamma certificate holds for every generic `τ` with a level-`f` vector and
central character `ω_τ`, with constant `C(ω_τ)`. Then the hypothesis `hshell` of
`rightAverage_eq_target_of_shells` holds for `F_A = corankRestriction F ψ Fbig` and the single
constant `c = shellConstant(ω₀)`. Cases:
- `w_avg = 0`: the left side vanishes, and `vol(K⁰(f)) ∫ t w = ∫_(K⁰(f)) ω(k₀₀) w_avg = 0`.
- `w_avg ≠ 0`: `π` has a central character (`exists_quasicharacter_hasGLCentralCharacter`). It
  equals `ω⁻¹` on the units (`centralCharacter_eq_inv_of_model` with `inverseAverage_scalar`).
  - `j ≠ 0`: `shell_average_identity` for `π`.
  - `j = 0`: write `ω₀ = ω_π ν^(m+1)` with `ν` unramified
    (`exists_unramified_pow_of_eq_on_units`). Apply `shell_average_identity` to
    `π' = π ⊗ (ν ∘ det)`. It is generic with a level-`f` vector and central character `ω₀`
    (`unramifiedTwist_properties`). Use the twisted functional and model vector
    `w'(g) = ν(det g) w(g)` (published `twistFunctional`, `twistModelLinearMap`). Since
    `w'_avg = ν(det) w_avg`, and `ν(det g) = 1` on the shell `ord det = 0` and on `N K⁰(f)`,
    both sides for `(π', w')` equal those for `(π, w)`.
