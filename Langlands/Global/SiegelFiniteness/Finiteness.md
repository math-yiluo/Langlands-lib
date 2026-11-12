# Factors of a rational matrix relating two Siegel points

Module: `Langlands.Global.SiegelFiniteness.Finiteness`. Provenance: internal.

- `middle_apply`: for the middle factor `M = diag(ω') A_{x'} m A_x⁻¹ diag(ω)⁻¹`,
  `M_{ab} = realScale(e^{x'_a - x_b}) · (ω'_a m_{ab} ω_b⁻¹)` (diagonal matrices act on rows and
  columns; `realScale_mul`).
- `middleSet F n C Λ`: the image of `[0, e^Λ] × Z` under `(ρ, z) ↦ realScale ρ · z`, where `Z`
  is the union over `a, b` of the images of `C × K_std × C` under
  `(ω', m, ω) ↦ ω' m_{ab} ω⁻¹`; `isCompact_middleSet`.
- `entrySet F n ΩN C Λ`: the union over `i, j` of the images of
  `ΩN × (middleSet)^{n×n} × ΩN` under `(N', M, N) ↦ (N' M adj N)_{ij}`; `isCompact_entrySet`.
- `isUpperTriangular_diagonalGL`, `isUpperTriangular_diagonalGL_inv`,
  `isUpperTriangular_torus`, `isUpperTriangular_inv`: diagonal and torus factors and inverses
  of upper triangular invertible matrices are upper triangular.
- `inv_val_eq_adjugate`: a unitriangular invertible matrix has inverse its adjugate.
- `isBlockUpper_compactPart`: if `γ (N diag(ω) A_x κ) = N' diag(ω') A_{x'} κ'` with `N, N'`
  upper triangular and `γ` satisfies `IsBlockUpper s`, then so does `κ' κ⁻¹ =
  A_{x'}⁻¹ diag(ω')⁻¹ N'⁻¹ γ N diag(ω) A_x` (closure under products).
