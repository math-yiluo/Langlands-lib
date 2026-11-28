# Entries of block unipotent radicals

The module `Langlands.Group.GL.UnipotentEntries` describes the unipotent radical
`BlockShape.unipotentSubgroup` of a standard block parabolic subgroup of `GL_n(R)`, for a
commutative ring `R` and a block shape `B` of `n` (module `Langlands.Group.GL.Blocks`), by the
entries of `g - 1`, and proves that for at most two blocks the radical is commutative.

## Contents

- `BlockShape.upperBlocks R S`: for an `S`-module structure on `R`, the `S`-submodule of
  `Matrix (Fin n) (Fin n) R` of the matrices `Y` with `Y (indexEquiv x) (indexEquiv y) = 0`
  whenever the block of `x` does not precede the block of `y` (`¬ x.1 < y.1`): the matrices whose
  blocks on and below the diagonal vanish. `mem_upperBlocks` unfolds the membership.
- `BlockShape.mem_unipotentSubgroup_iff_sub_one_mem`: `g ∈ B.unipotentSubgroup R` if and only if
  `(g : Matrix) - 1 ∈ B.upperBlocks R S`. The proof combines `mem_unipotentSubgroup_iff` and
  `mem_parabolic_iff` (module `Langlands.Group.GL.Blocks`): blocks strictly below the diagonal
  vanish, diagonal blocks are identity matrices, and the entries of the identity matrix between
  distinct blocks are `0`.
- `BlockShape.upperBlocks_mul_eq_zero`: if `B.length ≤ 2`, the product of two matrices of
  `upperBlocks` is `0`. A nonzero term `Y_{xz} Z_{zy}` of the product would need blocks
  `x.1 < z.1 < y.1`, impossible among at most two blocks.
- `BlockShape.unipotentSubgroup_mul_comm`: if `B.length ≤ 2`, elements `a, b` of the unipotent
  radical commute. With `(a - 1)(b - 1) = 0 = (b - 1)(a - 1)`, both `ab` and `ba` equal
  `a + b - 1`.
- `BlockShape.map_mem_unipotentSubgroup`: a ring endomorphism `f` of `R`, applied entrywise
  (`Matrix.GeneralLinearGroup.map f`), preserves the unipotent radical, since `f` fixes the
  entries `0` and `1` of the identity matrix.

## Provenance

These are elementary facts about block matrices, formulated for this Library. In the two-block
case `(k, n - k)` they say that the unipotent radical consists of the matrices
`[[1, X], [0, 1]]` with `X` a `k × (n - k)` matrix, and that `X` adds under multiplication.
