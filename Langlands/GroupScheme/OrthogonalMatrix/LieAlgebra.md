# Matrix coordinates on the Lie algebra of the split orthogonal group

This internal module identifies the Lie algebra of the split orthogonal group
`OrthogonalMatrix.groupScheme l R` (Gram matrix `Q = [[0, 1], [0, 0]]` on `l ⊕ l`,
polar matrix `J = Q + Qᵀ`) with a space of matrices. It follows the published module
`SymplecticMatrix.LieAlgebra`.

## The Lie condition in coordinates

- `mul_formMatrix_apply_inl/_inr`, `formMatrix_mul_transpose_apply_inl/_inr`: the
  entries of `Y Q` and `Q Yᵀ`.
- `isAlt_lie_iff`: `Y Q + Q Yᵀ` is alternating if and only if `Y J + J Yᵀ = 0` and
  `Y (inl a) (inr a) = Y (inr a) (inl a) = 0` for every `a`. The diagonal of
  `Y Q + Q Yᵀ` at `inl a` is `Y (inl a) (inr a)` and at `inr a` it is
  `Y (inr a) (inl a)`; the published `isAlt_iff` characterizes alternating matrices
  as those with `M + Mᵀ = 0` and zero diagonal.

## Dual-number orthogonal matrices

- `defect_one_add_epsilonMatrix`: `(1 + εY) Q (1 + εY)ᵀ - Q = ε (Y Q + Q Yᵀ)`, using
  `ε² = 0`.
- `isAlt_epsilonMatrix_iff`: an `ε`-matrix `εM` is alternating exactly when `M` is
  (take second components of a witness `V` with `εM = V - Vᵀ`).
- `one_add_epsilonMatrix_mem_iff`: `1 + εY` is orthogonal over `A[ε]` exactly when
  `Y Q + Q Yᵀ` is alternating.

## Affine points and Lie coordinates

- `affinePointsEquiv l R S`: points over `Spec S` are the orthogonal matrices over `S`
  (from the corepresentability API); `affinePointsEquiv_inclusion` and
  `affinePointsEquiv_leviMap` compute the inclusion into `GL_{l ⊕ l}` and the Levi
  embedding on these points.
- `lieMatrix`: the `A`-linear map from the Lie kernel of `O_{2l}` over `A[ε]` to
  matrices, the composite of the Lie map of the inclusion into `GL_{l ⊕ l}` with the
  published `GeneralLinear.DualNumber.pointKernelLinearEquiv`.
- `mono_inclusion`: the inclusion into `GL_{l ⊕ l}` is a monomorphism of schemes, so
  `lieMatrix_injective` holds.
- `affinePointsEquiv_lieKernel`: the dual-number point of a Lie kernel element `X` is
  `1 + ε lieMatrix X`.
- `isAlt_lieMatrix`: every `lieMatrix X` satisfies the Lie condition;
  `exists_lieMatrix_eq`: conversely every matrix satisfying it is `lieMatrix X` for some
  `X`, built from the dual-number point `1 + εY`.

These are the standard description of the Lie algebra `𝔬(Q)` as the matrices `Y` with
`Y J + J Yᵀ = 0` whose quadratic part `Y Q + Q Yᵀ` has zero diagonal (the additional
diagonal conditions matter in characteristic `2`).
