# The opposite open cell of `GL_n` for a weight vector: matrix algebra

This internal unit contains the matrix algebra behind the opposite open cell of a general
linear group. Throughout, `n` is a finite index type, `A` an arbitrary commutative ring and
`e : n → ℤ` a weight vector. The two subgroups are the ones from `Dynamic.GeneralLinear`:

* `blockUnipotentSubgroup A (-e)`: the invertible matrices whose entry `(i, j)` equals the
  identity entry whenever `e j ≤ e i`. Off the diagonal they are supported on the pairs with
  `e i < e j`.
* `blockParabolicSubgroup A e`: the invertible matrices whose entry `(i, j)` vanishes whenever
  `e i < e j`.

## Threshold blocks and the cell minor

For an integer `c`, the upper threshold set is `S_c = {l | c ≤ e l}`.

* `thresholdBlock e c M` is the square block of `M` on `S_c`.
* `thresholdColumns e c M` is the `n × S_c` matrix of the columns of `M` in `S_c`.
* `cellMinor e M`, written `δ_e(M)`, is the product of `det (thresholdBlock e c M)` over the
  values `c` of `e`.

`map_cellMinor` states that a ring homomorphism `f` commutes with the cell minor:
`f (δ_e(M)) = δ_e(M.map f)`.
`isUnit_thresholdBlock_of_isUnit_cellMinor` states that if `δ_e(M)` is a unit, then so is every
factor `det (thresholdBlock e (e j) M)`.

`thresholdBlock_mul_of_left` and `thresholdBlock_mul_of_right` compute the threshold block of a
product. When `X` has no entries from rows in `S_c` to columns outside `S_c`, the `S_c` block of
`X * Y` is the product of the `S_c` blocks. The same holds when `Y` has no entries from rows
outside `S_c` to columns in `S_c`. The proof splits the sum over the middle index into
`S_c` and its complement, and the complement sum vanishes.

## Products `u p`

`isUnit_det_thresholdBlock_of_unipotent` states that every threshold block of a matrix `u` in
`blockUnipotentSubgroup A (-e)` has unit determinant. Both `u` and `u⁻¹` satisfy the left-factor
hypothesis, so the `S_c` block of `u u⁻¹ = 1` is the product of the `S_c` blocks of `u` and
`u⁻¹`. `isUnit_det_thresholdBlock_of_parabolic` states the same for `blockParabolicSubgroup A e`,
using the right-factor hypothesis for `p⁻¹ p = 1`.

`isUnit_cellMinor_mul` states that `δ_e(u p)` is a unit for such `u` and `p`. A parabolic `p`
satisfies the right-factor hypothesis, so every threshold block of `u p` is the product of the
threshold blocks of `u` and `p`, and both have unit determinant.

`blockUnipotentSubgroup_neg_inf_blockParabolicSubgroup` states that the two subgroups meet
trivially: a matrix in both has identity entries where `e j ≤ e i`, and zero entries where
`e i < e j`.

## The cell decomposition

`exists_cell_decomposition` states that if `δ_e(g)` is a unit for `g : GL n A`, then `g = u p`
with `u` in `blockUnipotentSubgroup A (-e)` and `p` in `blockParabolicSubgroup A e`.

The proof constructs `u` explicitly. Every threshold block of `g` is invertible. Set
`cellRatio e c g = (thresholdColumns e c g) (thresholdBlock e c g)⁻¹`, an `n × S_c` matrix whose
rows in `S_c` form the identity (`cellRatio_of_le`). For `c ≤ c'`, the matrix
`cellRatio e c' g` equals `cellRatio e c g` times its own rows in `S_c` (`cellRatio_eq_mul`).
The matrix `cellLower e g` has as column `j` the column `j` of `cellRatio e (e j) g`.

* By `cellLower_of_le`, its entry `(i, j)` is the identity entry when `e j ≤ e i`. This is
  exactly membership in `blockUnipotentSubgroup A (-e)` (`cellLowerUnit_mem`).
* It is block triangular with identity diagonal blocks, so its determinant is `1`
  (`det_cellLower`). This makes it the invertible matrix `cellLowerUnit`.
* By `cellLower_columns`, its columns in `S_c` are `cellRatio e c g` times its own block on
  `S_c`. This uses `cellRatio_eq_mul`.

Set `p = u⁻¹ g`. Fix `i, j` with `e i < e j` and write `S = S_{e j}`. The column identity gives
`u⁻¹ (cellRatio e (e j) g) = 1_{:,S} (u_{SS})⁻¹`, whose row `i` vanishes because `i ∉ S`.
Since column `j` of `g` is column `j` of `(cellRatio e (e j) g) g_{SS}`, the entry `p i j`
vanishes. So `p` is block parabolic for `e`.

## Provenance

Step 3 of the proof of Proposition 2.1.8(3) in Conrad–Gabber–Prasad, *Pseudo-reductive groups*
(2nd edition), starts from the open cell of `GL(V)`, which the book takes from its Example 2.1.1
and Proposition 2.1.2. This unit supplies the matrix algebra of that case for a diagonal
cocharacter with weights `e`. The cell minor `δ_e`, the threshold blocks and the explicit factor
`cellLower` are an internal formulation, not taken from the book.
