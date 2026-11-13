# Isotropy of Hermitian spaces over quadratic extensions of local fields

Author: Worker 166.

This module proves Hermitian consequences of the published anisotropic quadratic
dimension bound. Here `K` is a nonarchimedean local field (`IsNonarchimedeanLocalField`
with its `ValuativeRel` and topology), and `L/K` is a separable quadratic extension
with involution `SU3Root.fieldInvolution K L`. Any characteristic is allowed,
including residue characteristic two and characteristic two. Conventions for the
pairing `h`, Hermitian symmetry `hbar`, `DiagonalForm`, `Index` and `gram` follow
`HermitianNondegenerateCoordinates`. The module is linear algebra for Task 5973 and
does not prove `LocalAnisotropicTypeAInnerStatement`.

## Statements

- `DiagonalForm.card_le_two_of_isAnisotropic`: an anisotropic diagonal Hermitian form
  `H` on a finite index type `ι` has `Fintype.card ι ≤ 2`.
- `local_anisotropic_finrank_le_two`: a finite-dimensional Hermitian space with
  `h x x = 0 → x = 0` has `finrank L V ≤ 2`.
- `local_exists_isotropic`: a finite-dimensional Hermitian space with
  `3 ≤ finrank L V` has a nonzero vector `x` with `h x x = 0`. Nondegeneracy is not
  needed.
- `local_exists_hyperbolic_diagonal_coordinates`: a nondegenerate Hermitian space with
  `finrank L V = m + 2` and `1 ≤ m` has hyperbolic-plus-diagonal coordinates
  `V ≃ₗ[L] L × ((Fin m → L) × L)`, with a diagonal middle form on `Fin m` whose
  weights are nonzero.
- `local_exists_gram_basis`: under the same hypotheses there is a diagonal form `H`
  on `Fin m` with nonzero weights and a basis `b : Basis (Index (Fin m)) L V` with
  `h (b i) (b j) = gram H i j`.
- `local_exists_gram_congruence`: let `M` be a matrix on `Index (Fin m)` over `L`
  with `1 ≤ m`, `conjugateTranspose (fieldInvolution K L) M = M` and `M.det ≠ 0`.
  Then there is a diagonal form `H` on `Fin m` with nonzero weights and
  `P : Matrix.GeneralLinearGroup (Index (Fin m)) L` such that
  `conjugateTranspose (fieldInvolution K L) P * M * P = gram H`.

The last statement has the shape of the congruence hypothesis of the published
`HermitianRoot.SchemeModel.isometryIso`, taking the matrix `gram J` as `M`.

## Proofs

For `DiagonalForm.card_le_two_of_isAnisotropic`, the published
`DiagonalForm.quadraticForm K L` is a `K`-quadratic form on `ι → L` whose zeros are
the zeros of the Hermitian self-pairing (`quadraticForm_anisotropic_iff`). The
underlying `K`-space has dimension `2 * Fintype.card ι` (`quadraticForm_finrank`).
The published theorem `localQuadraticAnisotropicDimensionBound` gives dimension at
most four, so `card ι ≤ 2`.

`local_anisotropic_finrank_le_two` diagonalizes the anisotropic space with the
published `exists_anisotropic_diagonal_coordinates` and applies the previous lemma.
`local_exists_isotropic` is the contrapositive.

`local_exists_hyperbolic_diagonal_coordinates` and `local_exists_gram_basis` combine
`local_exists_isotropic` (the dimension is `m + 2 ≥ 3`) with
`exists_isotropic_diagonal_coordinates` and `exists_isotropic_gram_basis` from
`HermitianNondegenerateCoordinates`.

For `local_exists_gram_congruence`, apply `local_exists_gram_basis` to
`matrixHermitianPairing K M` on `Index (Fin m) → L`, which has dimension `m + 2`. That
pairing is Hermitian and nondegenerate by `matrixHermitianPairing_bar` and
`matrixHermitianPairing_nondegenerate`. The matrix `P` is
`(Pi.basisFun L _).toMatrix b`, whose columns are the basis vectors `b j`. Its
inverse is `b.toMatrix (Pi.basisFun L _)`, from Mathlib's
`Basis.toMatrix_mul_toMatrix_flip`. By `conjugateTranspose_mul_mul_apply`, entry
`(i, j)` of `Pᴴ M P` is the pairing of `b j` with `b i`, which equals
`gram H j i = gram H i j` by `gram_apply_comm`.

## Provenance

The fact that a Hermitian form of dimension at least three over a quadratic extension
of a nonarchimedean local field is isotropic is classical. This module derives it
internally from the published quadratic bound by passing to the trace form over `K`.
It does not transcribe an external proof. The other statements are internal
elementary consequences, chosen to match the matrix convention of
`HermitianRoot.SchemeModel`.
