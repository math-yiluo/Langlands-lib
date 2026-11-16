# The theta series of a row function

Module `Langlands.Global.RankinSelberg.EqualAnalyticTheta`, namespace
`Langlands.Global.RankinSelbergGlobal.EqualAnalytic`.

For `Φ : 𝔸^n → ℂ` and `M ∈ GL_n(𝔸)`:

- `thetaSum F n Φ M = Σ'_(ξ ∈ F^n, ξ ≠ 0) Φ(ξ M)`, the unconditional sum written over all
  `ξ : RatRow F n` with the term `0` at `ξ = 0`. This is `Θ'_Φ` in the notation of Cogdell 2004,
  printed p.209.
- `thetaNorm F n Φ M = Σ'_(ξ ≠ 0) ‖Φ(ξ M)‖` in `[0, ∞]`, and `‖thetaSum‖ ≤ thetaNorm`
  (`enorm_thetaSum_le`).

## Results

- `summable_rowMul`, `thetaSum_add`: for dominated `Φ`, `Σ_ξ Φ(ξ M)` converges and
  `Θ(Φ, M) + Φ(0) = Σ_ξ Φ(ξ M)`.
- **`thetaSum_poisson`**: for `Φ ∈ S(𝔸^n)` and a standard character `ψ`,
  `Θ(Φ, M) + Φ(0) = |det M|⁻¹ (Θ(Φ̂, ᵗM⁻¹) + Φ̂(0))`. This is the Part A theorem
  `hasSum_poisson_mul` with the term `ξ = 0` split off on both sides.
- `thetaSum_rational_mul`, `thetaNorm_rational_mul`: invariance under `M ↦ γ M` for
  `γ ∈ GL_n(F)`. `ξ ↦ ξ γ` is a bijection of `F^n ∖ 0` (`ratRowMulEquiv`).
- `stronglyMeasurable_thetaSum`, `measurable_thetaNorm`: measurability on the adelic points,
  for continuous `Φ`, via Mathlib's `StronglyMeasurable.tsum`.

## Provenance

The theta series and its Poisson summation formula are as in Cogdell 2004, §2.3, printed
p.209. The proofs are internal and rest on the Part A Poisson formula.
`ratRow_countable` is an instance; `ratRowMulEquiv` and `continuous_rowMul_term` are internal.
