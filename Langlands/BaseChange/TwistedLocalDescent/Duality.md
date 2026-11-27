# The twisted discriminant on the opposite nilradical

Module `Langlands.BaseChange.TwistedLocalDescent.Duality`. Let `E/F` be a finite separable field
extension, `σ` an `F`-automorphism of `E`, `B` a block shape of size `n` with standard Levi `M`
and `m ∈ M(E)`.

## Subspaces of `M_n(E)`

- `lowerLie B` (`𝔲̄`): matrices whose entries vanish unless the row block is strictly larger
  than the column block; `lowerParabolicLie B` (`𝔭̄`): block lower triangular matrices.
  `lowerParabolicLie_eq_sup`: `𝔭̄ = 𝔪 ⊕ 𝔲̄`, with `𝔪` the block diagonal matrices
  (`blockDiagonalLieSubmodule` of the Library); `disjoint_blockDiagonalLieSubmodule_lowerLie`.
- Conjugation by a block diagonal element preserves block shapes:
  `linearAdjoint_mem_lowerLie`, `linearAdjoint_mem_lowerParabolicLie`,
  `linearAdjoint_mem_blockDiagonalLieSubmodule`.

## Operators

- `matrixSigma σ`: entrywise `σ`, an `F`-linear map.
- `twistedOperator B σ m = σ − Ad(m)⁻¹`, `X ↦ σ(X) − m⁻¹ X m`, and
  `twistedAdjointOperator B σ m = σ⁻¹ − Ad(m)`; both preserve `𝔲̄`, `𝔭̄` and `𝔪`.

## Trace duality

`tracePairing X Y = Tr_{E/F}(tr(X Y))`. `tracePairing_adjoint`: `T` and `T'` are adjoint for this
pairing (`Tr_{E/F} ∘ σ = Tr_{E/F}` and the trace is invariant under conjugation).
`tracePairing_lowerParabolicLie_lowerLie`: `𝔭̄` and `𝔲̄` pair to zero (a product of a block lower
triangular and a strictly block lower matrix has zero trace). `tracePairing_separating` and
`mem_lowerParabolicLie_of_tracePairing` use the nondegeneracy of `Tr_{E/F}` (separability).

## Decomposition of the discriminant

The Library's `twistedRelativeParabolicDiscriminant B σ m` is the determinant over `F` of `T` on
`𝔤/𝔪`.

- `twistedRelativeParabolicDiscriminant_eq_det_mapQ`: the same determinant computed on the
  quotient by `𝔪` viewed as an `F`-subspace.
- `twistedRelativeParabolicDiscriminant_eq_mul_det_quotient`: it is `det(T | 𝔲̄) · det(T | 𝔤/𝔭̄)`
  (`det_mapQ_eq_det_restrict_mul_det_mapQ`).
- `twistedRelativeParabolicDiscriminant_eq_mul`: `D_{G/M,σ}(m) = det(T | 𝔲̄) · det(T' | 𝔲̄)`, from
  the trace duality between `𝔤/𝔭̄` and `𝔲̄` (`det_mapQ_eq_det_restrict_of_pairing`).
- `det_twistedAdjointOperator_restrict`: `T' = −Ad(m) ∘ T ∘ σ⁻¹` on `𝔲̄`
  (`twistedAdjointOperator_restrict_eq`), so `det(T' | 𝔲̄) = det(−Ad(m)) det(T) det(σ⁻¹)` on `𝔲̄`.
- `abv_det_matrixSigma_restrict`: `σ` of finite order has determinant of absolute value one on
  `𝔲̄` (a power of the determinant is `1`).
- `abv_twistedRelativeParabolicDiscriminant`: for an absolute value `abv` on `F` and `σ` of
  finite order, `abv(D_{G/M,σ}(m)) = abv(det(T | 𝔲̄))² · abv(det_F(Ad(m) | 𝔲̄))`.
