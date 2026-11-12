# Maximality of the diagonal torus of `Sp` and its long roots

This internal module shows that the diagonal torus `diagonalTorus l k` of
`SymplecticMatrix.Torus` is a maximal torus of the split symplectic group over a field `k`.
It also shows that each long root `2e_a` is a root. Matrices are indexed by `l ⊕ l`, and
`J = Matrix.J l A = [[0, -1], [1, 0]]` is Mathlib's standard form. The weights `w(x)` are
`weightCoord l x` (`e_a` at `inl a`, `-e_a` at `inr a`).

## The Lie condition in entries (any commutative ring)

* `mul_J_apply_inl`, `mul_J_apply_inr`, `J_mul_apply_inl`, `J_mul_apply_inr` (`@[simp]`): the
  entries of `Y J` and `J M`. Multiplying by `J` swaps the two blocks of columns, resp. rows,
  with a sign.
* `lie_condition_iff`: write `Y = [[a, b], [c, d]]` in blocks. Then `Y J + J Yᵀ = 0` holds
  exactly when `b` is symmetric, `d = -aᵀ` and `c` is symmetric. In entries:
  `Y (inl i) (inr j) = Y (inl j) (inr i)`, `Y (inr i) (inr j) = -Y (inl j) (inl i)` and
  `Y (inr i) (inl j) = Y (inr j) (inl i)`.
* `diagonal_mul_J_add`: every `diag(d, -d)` satisfies the Lie condition.

## Coordinates of weight differences

* `eq_of_weightCoord_sub_apply_eq_two`: if `w(x) - w(y)` has coordinate `2` at `b`, then
  `x = inl b` and `y = inr b`.
* `weightCoord_inl_sub_inr`: `w(inl b) - w(inr b) = 2e_b`.

## Maximality over a field

Let `k` be a field and `𝔻` the split torus `splitTorus.commGroupScheme (Spec k) (ULift l)`,
the source of `diagonalTorus l k`.

* `mem_weightSpace_zero_iff`: an element `X` of the Lie algebra lies in the zero weight space
  exactly when `lieMatrix X` is diagonal. This is `mem_weightSpace_diagonalTorus_iff_support`
  with `χ = 0` and `weightCoord_injective`.
* `zeroWeightCoord l k`: the `k`-linear map from the zero weight space to `l → k` that reads
  off the upper-left diagonal entries `X_{inl a, inl a}`. `zeroWeightCoord_apply` restates
  this.
* `lieMatrix_eq_zero_of_zeroWeightCoord`: an element of the zero weight space with vanishing
  upper diagonal has zero matrix. The off-diagonal entries vanish because the matrix is
  diagonal. The lower diagonal entries are the negatives of the upper ones by
  `lie_condition_iff`.
* `zeroWeightCoord_bijective`: injectivity follows from the previous lemma and
  `lieMatrix_injective`. For surjectivity, `diag(d, -d)` is a Lie algebra element
  (`exists_lieMatrix_eq`, `diagonal_mul_J_add`) of weight zero.
* `finrank_weightSpace_zero`: the zero weight space has dimension `card l`.
* `isMaximalTorus_diagonalTorus l k` (**maximality**): the diagonal torus is a maximal torus,
  in the sense of the Library's `IsMaximalTorus`. The Library's criterion
  `isMaximalTorus_of_finrank_zeroWeight` applies to a split torus that is a closed subgroup of
  a smooth, affine, connected group. It requires the zero weight space to have the dimension
  of the Lie algebra of the torus, which is `card l` (`splitTorus.finrank_lieKernel`). The
  group is connected by the Library's `connectedSpace_groupScheme`.

## Roots and long roots

The roots are the Library's `roots (diagonalTorus l k)`: the nonzero characters with nonzero
weight space. Coordinates of characters are `GeneralLinear.characterCoordEquiv l k`.

* `exists_coord_of_mem_roots`: every root has coordinates `w(x) - w(y)` for some `x`, `y`.
  Choose a nonzero element of the root space and a nonzero entry of its matrix, then use
  `mem_weightSpace_diagonalTorus_iff_support`.
* `eq_single_two_of_mem_roots`: a root with coordinate `2` at `b` has coordinates exactly
  `2e_b`.
* `longRoot l k a`: the character with coordinates `2e_a`. `characterCoordEquiv_longRoot`
  restates this.
* `single_inl_inr_mul_J_add`: the matrix unit at `(inl a, inr a)` satisfies the Lie
  condition.
* `longRoot_mem_roots`: `2e_a` is a root. It is nonzero, and the Lie algebra element with
  matrix the unit at `(inl a, inr a)` is a nonzero element of its weight space.

No assumption is made on `l` or on the characteristic of `k`.

## Provenance

These are standard facts about the split symplectic group: the diagonal torus is maximal,
and the long roots `2e_a` are roots. The module is internal. The proofs were written for it
from the cited Library results. Maximality uses the Library's zero-weight-space criterion,
so this module computes no centralizer directly.
