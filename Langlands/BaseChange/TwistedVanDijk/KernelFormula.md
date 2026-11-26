# The kernel formula for the induced twisted operator

Module `Langlands.BaseChange.TwistedVanDijk.KernelFormula`. With the notation of
`Langlands.BaseChange.TwistedVanDijk.Operator`, let `π` be the normalized product induction
`LocalFieldData.normalizedProductInduced B P` and `ι(A) = inducedSigmaIntertwiner σ B A`, which
sends a smooth induced function `ξ` to `x ↦ (A₁ ⊗ ⋯ ⊗ A_r)(ξ(σ⁻¹(x)))`. The module computes
`π(φ) ι(A) ξ` on vectors fixed by a level of `φ`.

## Auxiliary results

- `exists_isCompact_iwasawa_preimage`: for a compact `C ⊆ G` there is a compact `S ⊆ M × U`
  containing every `(m, u)` with `m u k ∈ C` for some `k ∈ K`. Take `S` the preimage under the
  homeomorphism `parabolicProductHomeomorph` of the compact set `P ∩ C K⁻¹`.
- `evalLinear B g` is evaluation at `g` of smooth induced functions, as a linear map;
  `isLocallyConstant_eval`: `g ↦ ξ(g)` is locally constant (right invariance under an open
  subgroup, `Induction.exists_openSubgroup_eval_mul`).

## The kernel formula

`eval_integratedAction_inducedSigmaIntertwiner`: with Haar measures `μG`, `μM`, `μU` of volume
one on `K`, `M(𝒪_E)`, `U ∩ K` and the Haar probability measure `μK` on `K`, a level `L` of `φ`
and a `K'`-fixed smooth induced function `ξ`,

`(π(φ) ι(A) ξ)(g) = ∑_{x ∈ K/K'} c (A₁ ⊗ ⋯ ⊗ A_r) τ(k(g, rep x)) ξ(rep x)`,

the right side being `compactSum ... L (x ↦ ξ(rep x)) g`, with `c = μK(K')` and `k` the kernel
of `Langlands.BaseChange.TwistedVanDijk.KernelFunction`.

The proof compares both sides after applying an arbitrary linear form `Λ` on `⊗ W_i`
(`Module.eval_apply_injective`); write `ℓ = Λ ∘ (A₁ ⊗ ⋯ ⊗ A_r)`.

1. `Hecke.integratedAction_dual` gives
   `Λ((π(φ) ι(A) ξ)(g)) = ∫_G φ(h) ℓ(ξ(σ⁻¹(g h))) dh`.
2. The substitution `h = g⁻¹ σ(h')` preserves `μG` (`map_entrywiseAut_eq` and left
   invariance), giving `∫_G φ(g⁻¹ σ(h')) ℓ(ξ(h')) dh'`.
3. The Iwasawa decomposition `dg = dm du dk` (`iwasawa_measure_eq`) turns this into an integral
   over `(M × U) × K`. The integrand is continuous and vanishes unless `(m, u)` lies in the
   compact set given by `exists_isCompact_iwasawa_preimage`, so it is integrable.
4. Covariance of `ξ` (`normalizedProductInduced_covariant`):
   `ξ(m u k) = δ_P(m)^{1/2} τ(m) ξ(k)`.
5. Fubini (`integral_prod_symm`, then `integral_prod`) integrates over `M × U` first, for each
   `k ∈ K`; the inner integral is
   `∫_M δ_P(m)^{1/2} ∫_U φ(g⁻¹ σ(m u k)) du · ℓ(τ(m) ξ(k)) dm = ℓ(τ(k(g, k)) ξ(k))`
   by `Hecke.integratedAction_dual` for `τ`.
6. The function `k ↦ ℓ(τ(k(g, k)) ξ(k))` on `K` is right invariant under `K'`
   (`kernelTest_mul_right_right` and the `K'`-invariance of `ξ`), so its integral is the finite
   sum `∑_x c ℓ(τ(k(g, rep x)) ξ(rep x))` (`integral_eq_sum_quotient_out`).
