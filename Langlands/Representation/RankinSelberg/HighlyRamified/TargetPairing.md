# Pairings with the target function

Internal helper for the proof of `HighlyRamifiedGammaStabilityStatement` (Jacquet–Shalika 1985,
§4.4, printed page 329, the right-hand side of (13)). It relates the target `t` of
`DualTarget` to the `K⁰(f)`-integrals produced by `dual_shell_integral`. The target is
`t(u k) = ψ_N(u) ω(k₀₀)` on `N K⁰(f)` and `0` off it.

## Algebra (any field with a valuative relation)

- `firstEntry_mul_firstColumn`: `(k₁ k)₀₀ ≡ k₁₀₀ k₀₀` modulo `𝔭^f` for `k₁, k ∈ K⁰(f)`.
- `omega_firstEntry_mul`: hence `ω((k₁ k)₀₀) = ω(k₁₀₀) ω(k₀₀)` when `ω` is trivial on `1 + 𝔭^f`.
- `firstColumnTarget_mul_firstColumn`: `t(g k) = t(g) ω(k₀₀)` for `k ∈ K⁰(f)`.

## Measure (canonical p-adic structures, published `generalLinearHaar` and
`unipotentQuotientHaar`)

- `integrable_out_of_compact_support`: a left `N`-invariant function that is right invariant
  under an open subgroup and supported in `N C`, `C` compact, is integrable on
  `N \ GL_(m+1)` through representatives. It descends to a continuous function on the
  Hausdorff quotient (published `leftQuotient_t2Space`, `leftQuotient_isOpenQuotientMap`)
  with compact support.
- `rightAverage_firstColumnTarget`: the weighted right average of `t` (weight
  `firstColumnWeight`, i.e. `ω(k₀₀)⁻¹` on `K⁰(f)`) is `vol(K⁰(f)) · t`.
- `integral_firstColumnTarget_pair`: for `W` right invariant under an open subgroup with
  `W(u g) = ψ_N(u)⁻¹ W(g)`, `∫ t W = ∫_(K⁰(f)) ω(k₀₀) W(k) dk`. This is
  `integral_out_of_support` for `K⁰(f)`, with the published normalization `μ_N(N(O)) = 1`
  (`unipotentHaar_firstColumn`).
- `inverseAverage_apply`: `W_avg(g) = ∫ w(k) W(g k⁻¹) dk` for the inverse average of
  `DualAverage`. `inverseAverage_firstColumn_properties`: the inverse average with the weight of
  `K⁰(f)` keeps the left equivariance. It is right invariant under the principal congruence
  subgroup of level `f`, by right invariance of the Haar measure and of the weight.
- `integral_firstColumn_inverseAverage`:
  `∫_(K⁰(f)) ω(k₀₀) W_avg(k) dk = vol(K⁰(f)) ∫ t W`. The left side is `∫ t W_avg` by the
  previous item. The adjointness `integral_rightAverage_pair` turns it into
  `∫ (average of t) W`, and `rightAverage_firstColumnTarget` evaluates that average.
