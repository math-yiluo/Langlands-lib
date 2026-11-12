# The standard symplectic group scheme over a field

Author: Worker 118.

`Langlands.GroupScheme.Symplectic.groupScheme K n` is the actual affine group
scheme of isometries of the standard alternating form on a vector space of
dimension `2n`, for every field `K : Type u` and every natural number `n`.
Characteristic two and `n = 0` are allowed.

The Gram matrix is Mathlib's `Matrix.J (Fin n) K`, with blocks
`[[0, -1], [1, 0]]` on `(Fin n) ⊕ (Fin n)`. The coefficient involution
`scalarInvolution K` is the identity, so its matrix extension is transpose.
The group scheme specializes `Quaternionic.FirstKindInvolution.unitaryGroup`,
which is the affine closed isometry subgroup constructed in
`Quaternionic.IsometryCut`. It uses the full isometry group. The definition
does not add a reduced-norm condition.

`isAntihermitian_J` checks the trace-valued antihermitian condition directly:
transpose negates `J`, and each diagonal entry is zero. This argument remains
valid in characteristic two. `isUnit_J` uses Mathlib's invertibility of the
determinant of `J`. `inclusion` is the closed inclusion into the unit group
scheme of the full matrix algebra, and `isAffineHom_groupScheme` records its
affineness over the field.

`coefficientEquiv` identifies `R ⊗[K] M_s(K)` with `M_s(R)`, by the Library's
`FiniteAlgebraUnits.MatrixPoints.coefficientEquiv` followed by the tensor unit
isomorphism `R ⊗[K] K ≃ R`. Its formula on pure tensors is
`r ⊗ M ↦ (r · algebraMap(M_ij))`. The module proves that this map sends
`1 ⊗ J` to `J` and the extended involution to transpose.

For every test scheme `T` over `Spec K`, `ambientPointsEquiv` identifies the
points of the ambient unit group with invertible matrices over the global
sections of `T`. The theorem `mem_range_inclusion_iff` proves that the point
belongs to the symplectic subgroup exactly when its matrix `M` satisfies
`M J Mᵀ = J`, which is membership in Mathlib's `Matrix.symplecticGroup`.
It follows from the all-test point equation for the existing unitary cut and
the coefficient isomorphism.

This is an internal specialization and comparison of the published isometry
construction with Mathlib's symplectic matrices. No smoothness, connectedness,
reductivity, simple connectedness, almost simplicity, or root datum is claimed.
Those structural properties are separate proof obligations.
