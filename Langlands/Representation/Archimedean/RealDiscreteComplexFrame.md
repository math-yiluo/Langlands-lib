# The complex frame adapted to a block layout

Lean module: `Langlands.Representation.Archimedean.RealDiscreteComplexFrame`, part of the proof of
`Langlands.Archimedean.RealTiedDiscreteSeparatedScalarCommutantStatement` (the chain ends in
`RealDiscreteSeparatedProof`). All declarations are in the namespace
`Langlands.Archimedean.RealDiscreteFrame`.

## Purpose and provenance

The module proves no statement of record. It defines the concrete complex matrix `U` used in
the scalar step and proves the matrix identities that the abstract lemmas of
`RealDiscreteFrame` need. All declarations are internal; the computations are elementary
matrix algebra.

Layout. Fix `a ≤ n` with `n − a` even. Coordinates `l < a` are character coordinates. For
`r ≥ 0` the coordinates `p = a + 2r` and `p + 1` form a plane (the plane of an induction block).

## Declarations

* `mul_apply_eq_single`, `mul_apply_eq_pair`: an entry of `A B` when the column `k` of `B` has
  one, or two, possibly nonzero entries.
* `frameU n a`: the identity on character coordinates; on each plane `(p, p + 1)` the column
  `p` is `e_p + i e_{p+1}` (the `z`-column) and the column `p + 1` is `e_p − i e_{p+1}` (the
  `z̄`-column). `frameV n a`: the identity on character coordinates and the block
  `(1/2) [[1, −i], [1, i]]` on each plane. `frameU_apply`, `frameV_apply`, `frameU_char_col`,
  `frameU_z_col`, `frameU_zbar_col` give their entries.
* `exists_partner`, `frameV_col`, `frameV_col_char`: every column of `frameU` and `frameV`
  vanishes outside the column index and its plane partner.
* `frameU_mul_frameV` (`(n − a)` even): `frameU n a * frameV n a = 1`, checked entrywise with
  `mul_apply_eq_single` and `mul_apply_eq_pair`.
* `rotC p l`: `−1` if `l = p`, `1` if `l = p + 1`, `0` otherwise. `exp_rotC` evaluates
  `e^{i rotC(p, l) θ}`.
* `kmat_rot_apply`: the entries of the Library block rotation `blockRotation n p θ`
  (`cos θ` at `(p, p)` and `(p+1, p+1)`, `−sin θ` at `(p, p+1)`, `sin θ` at `(p+1, p)`, the
  identity elsewhere).
* `rot_col_char`, `rot_col_z`, `rot_col_zbar`, `kmat_rot_mul_frameU` (**rotation
  eigen-relation**): for a plane `p` (`a ≤ p`, `p − a` even, `p + 1 < n`),
  `r_p(θ) · U = U · diag(e^{i rotC(p, l) θ})`. On the `z`-column,
  `r_p(θ)(e_p + i e_{p+1}) = e^{−iθ}(e_p + i e_{p+1})`; on the `z̄`-column the factor is
  `e^{iθ}`; the other columns are fixed.
* `kmat_signDiagonal`, `toUnits_signDiagonal`: the complex matrix of the Library sign matrix
  `signDiagonal d` is `diag(sign(d_l))`, and as an element of `GL_n(ℝ)` it is the diagonal
  matrix of the signs.
* `diagonal_mul_frameU`: a diagonal matrix `diag(μ)` with `μ` constant on every plane commutes
  with `U`.
* `diagonal_flip_mul_frameU` (**flip**): the diagonal matrix with `−1` at `p + 1` and `1`
  elsewhere maps `U` to `U` with the columns `p` and `p + 1` exchanged, since
  `diag(1, −1)(e_p ± i e_{p+1}) = e_p ∓ i e_{p+1}`.
