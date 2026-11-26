# The kernel functions of the twisted van Dijk formula

Module `Langlands.BaseChange.TwistedVanDijk.KernelFunction`. With the notation of
`Langlands.BaseChange.TwistedVanDijk.Groups`, it defines the scalar kernel values and proves
their invariance, local constancy, compact support and covariance. The kernel of the induced
twisted operator `π(φ) ∘ ι(A)` in the compact model is obtained from them in
`Langlands.BaseChange.TwistedVanDijk.Operator`: the integrated action of the kernel value on the
Levi tensor representation, composed on the left with the tensor intertwiner `A₁ ⊗ ⋯ ⊗ A_r`.

## Conjugation of the unipotent radical

- `unipotentConj a` is the automorphism `y ↦ a y a⁻¹` of `U` for `a ∈ M`
  (`leviEmbedding_conj_mem_unipotentSubgroup'`), as an automorphism of topological groups.
- `map_unipotentConj_eq`: for `a` integral (`a ∈ M(𝒪_E)`), Haar measure on `U` is invariant
  under `unipotentConj a`, which preserves the compact open set `U ∩ K`
  (`map_eq_self_of_preimage_eq` of `Langlands.BaseChange.TwistedVanDijk.Measures`).

## Kernel values

For `φ : G → ℂ`, `g, y ∈ G` and `m ∈ M`,

`kernelValue σ B μU φ g y m = δ_P(m)^{1/2} ∫_U φ(g⁻¹ σ(m u y)) du`,

where `δ_P^{1/2}` is the Library's `leviHalfModulus` and `σ` acts entrywise.

- `kernelValue_mul_right_left`: if `φ` is left invariant under a subgroup `K'`, the kernel is
  right invariant in `g` under `K'`: `(g k)⁻¹ = k⁻¹ g⁻¹`.
- `kernelValue_mul_right_right`: if `φ` is right invariant under `K'` and `σ(K') ⊆ K'`, the
  kernel is right invariant in `y` under `K'`: `σ(m u y k) = σ(m u y) σ(k)`.
- `kernelStabilizer σ B K'' y` is the subgroup of `m₀ ∈ M` that are integral, satisfy
  `σ(y⁻¹ m₀ y) ∈ K''` and `δ_P(m₀) = 1`. `isOpen_kernelStabilizer`: it is open when `K''` is
  (the half modulus has open kernel, `isOpen_ker_leviHalfModulus`).
- `kernelValue_mul_stabilizer`: if `φ` is right invariant under `K''`, the kernel value is
  invariant under right translation of `m` by the kernel stabilizer. Write
  `m m₀ u y = m (m₀ u m₀⁻¹) y (y⁻¹ m₀ y)`; the last factor is absorbed by `φ` after `σ`, the
  substitution `u ↦ m₀ u m₀⁻¹` preserves `μU` (`map_unipotentConj_eq`), and `δ_P(m₀) = 1`.
- `isLocallyConstant_kernelValue`: for `φ` right invariant under an open subgroup, the kernel
  value is locally constant in `m` (`Induction.isLocallyConstant_of_mul_right` with the open
  kernel stabilizer).
- `hasCompactSupport_kernelValue`: for `φ` of compact support, the kernel value has compact
  support in `m`. The map `x ↦ g⁻¹ σ(x y)` is a homeomorphism of `G`, so the preimage `C` of
  the support of `φ` is compact; `C ∩ P` is compact (`P` is closed), its image under the Levi
  projection is compact, and the kernel value vanishes at every `m` outside this image, since
  then no `m u` lies in `C`.
- `kernelValue_entrywiseAut_mul`: covariance in `g`. For `q ∈ P` with Levi part `m_q`,
  `k(σ(q) g, y)(m) = δ_P(m_q)^{1/2} k(g, y)(m_q⁻¹ m)`. Write `q = m_q u_q`; then
  `q⁻¹ m u y = m' (c u) y` with `m' = m_q⁻¹ m` and `c = m'⁻¹ u_q⁻¹ m' ∈ U`, the substitution
  `u ↦ c u` preserves `μU`, and `δ_P(m) = δ_P(m_q) δ_P(m')`.
