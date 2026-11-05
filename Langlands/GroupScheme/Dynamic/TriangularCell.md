# Upper triangular points in the opposite cell

This internal unit supplies the matrix input for the pointwise use of the opposite cell in
the proof of `Torus.SolvableFixedContainmentConnectedStatement`. Throughout, upper triangular
means lying in `blockParabolicSubgroup A (fun i => -(i.val : ℤ))` for `GL (Fin N) A`, with `A`
an arbitrary commutative ring. By `mem_blockParabolicSubgroup` this says that the `(i, j)` entry
vanishes whenever `j < i`.

## Matrix statements

* `GeneralLinear.isUpperTriangular_of_mem_blockParabolicSubgroup`: such a matrix is
  `Matrix.IsUpperTriangular`. The inequality `-i < -j` is `j < i`.
* `GeneralLinear.isUnit_diag_of_mem_blockParabolicSubgroup`: its diagonal entries are units.
  The determinant of an invertible matrix is a unit, and Mathlib's
  `det_of_isUpperTriangular` writes it as the product of the diagonal entries. Each factor
  of a unit product is a unit.
* `GeneralLinear.isUnit_cellMinor_of_mem_blockParabolicSubgroup`: for every weight vector
  `e : Fin N → ℤ`, the cell minor `cellMinor e g` of such a matrix is a unit. The cell minor is
  the product of the determinants of the threshold blocks `{l | c ≤ e l}`. Each threshold block
  is a square block on a subset of `Fin N` with the induced order. It is again upper triangular,
  and its diagonal entries are diagonal entries of `g`. So each block determinant is a product of
  units.

## Pointwise cell decomposition

`Dynamic.exists_mem_parabolic_of_isUnit_cellMinor` works over a field `k : Type u`. Let `G` be
a group scheme over `Spec k` and `ρ : G ⟶ GL_n` a homomorphism whose underlying morphism of
schemes is a closed immersion. Let `χ` be a cocharacter with
`χ ≫ ρ = diagonalCocharacter n k e`. Let `x` be a point of `G` over an arbitrary test scheme
`T`, and assume the matrix of `x ≫ ρ` has unit cell minor for `e`. Then there is a point `p`
of `G` over `T` in `P(χ)` with `x * p⁻¹` in `U(χ⁻¹)`. Here `U(χ⁻¹)` is the dynamic unipotent
subgroup functor of `χ` precomposed with inversion on `𝔾_m`.

The proof repeats, at an arbitrary point instead of the generic point of the basic open, the
pointwise steps of the published `Dynamic.isOpenImmersion_mul_of_diagonal`:

1. `exists_cell_decomposition` factors the matrix as `u' p'`, with `u'` block unipotent for
   `-e` and `p'` block parabolic for `e`.
2. The stabilizer theorem `mem_zeroLocus_of_mul_mem` shows that `p'` is a zero of the
   equations `embeddingIdeal ρ` of `G`. Its other hypotheses are the published lemmas
   `ideal_le_embeddingIdeal`, `zeroLocusMulClosed_embeddingIdeal`,
   `one_mem_zeroLocus_embeddingIdeal` and `diagonalUnits_mem_zeroLocus_embeddingIdeal`.
3. `exists_comp_eq_of_mem_zeroLocus` lifts `p'` to a point `p` of `G`.
4. `mem_parabolic_iff_of_diagonal` and `mem_unipotent_iff_of_diagonal` translate the matrix
   memberships of `p'` and of `u' = (x ≫ ρ) p'⁻¹` into `p ∈ P(χ)` and `x * p⁻¹ ∈ U(χ⁻¹)`.

No monomorphism or representability hypothesis is needed for this pointwise statement.

## Provenance

The results are internal. They combine Mathlib's triangular determinant formula with the
published opposite-cell infrastructure of `Dynamic.GeneralLinearCell`,
`Dynamic.GeneralLinearStabilizer` and `Dynamic.OppositeCellEmbedding`. The decomposition follows
Step 3 of the proof of Conrad–Gabber–Prasad, *Pseudo-reductive groups* (2nd edition),
Proposition 2.1.8(3), as implemented in that published module.
