# Darboux normal form of alternating matrices over a field

This internal module proves the Darboux theorem over a field `L` in any characteristic: a
nondegenerate alternating form is equivalent to the standard symplectic form
`J = [[0, -1], [1, 0]]` (Mathlib's `Matrix.J`). It is a matrix lemma used to identify the
isometry group of an alternating form with the split symplectic group
`SymplecticMatrix.groupScheme`.

## Statements

* `nondegenerate_of_isAlt`: an alternating bilinear form that is left separating is
  nondegenerate (right separation follows from `B y x = -B x y`).
* `gramMatrix B v` is the Gram matrix `(B (v a) (v b))_{a b}` of a family of vectors (an
  auxiliary definition).
* `exists_symplecticFamily`: let `B` be a nondegenerate alternating bilinear form on a
  finite-dimensional vector space `V` (Mathlib's `LinearMap.BilinForm.IsAlt` and
  `Nondegenerate`). Then there are `k` with `2 k = dim V` and a family
  `v : Fin k ⊕ Fin k → V` with `gramMatrix B v = J`.
* `dotProduct_mulVec_self_eq_zero`: if `Cᵀ = -C` and `C` has zero diagonal, then
  `xᵀ C x = 0` for every `x`.
* `exists_mul_mul_transpose_eq_J` (**Darboux**): let `C` be a square matrix over `L`, indexed
  by any finite type `m`, with `Cᵀ = -C`, zero diagonal and `det C ≠ 0`. Then there are `k`,
  a rectangular matrix `P : Matrix (Fin k ⊕ Fin k) m L` and `P' : Matrix m (Fin k ⊕ Fin k) L`
  with `P P' = 1`, `P' P = 1` and `P C Pᵀ = J`.
* `mul_mul_mem_symplecticGroup_iff`: over any commutative ring, let `P' P = 1` and
  `P C Pᵀ = J`. Then `P g P'` is symplectic exactly when `g C gᵀ = C`.

## Proofs

`exists_symplecticFamily` is proved by strong induction on the dimension
(`exists_symplecticFamily_aux`, stated for all spaces of a given dimension). If the dimension
is positive, choose `x ≠ 0` and, by nondegeneracy, `y` with `B x y ≠ 0`. Rescale `y` to `f`
with `B x f = -1`, so `B f x = 1`. Pairing with `x` and `f` shows that `x`, `f` are linearly
independent and that `B` restricted to `W = span {x, f}` is nondegenerate. Mathlib's
`isCompl_orthogonal_of_restrict_nondegenerate`, `restrict_nondegenerate_iff_isCompl_orthogonal`
and `orthogonal_orthogonal` show that `V = W ⊕ W^⊥` and that `B` is nondegenerate on `W^⊥`.
`W^⊥` has dimension `dim V - 2`, so induction gives a family on `W^⊥`. Put `x`, `f` in front
of its two halves to get the family for `V`. Its Gram matrix is `J`, because `W^⊥` is
orthogonal to `x` and `f` on both sides.

`dotProduct_mulVec_self_eq_zero` uses `Finset.sum_involution` with the swap `(i, j) ↦ (j, i)`
on the double sum `∑ x_i C_ij x_j`. Swapped terms cancel because `C_ji = -C_ij`, and fixed
points are diagonal terms, which vanish. No division by `2` is needed.

For `exists_mul_mul_transpose_eq_J`, apply `exists_symplecticFamily` to the form
`Matrix.toBilin' C`. It is alternating by the previous lemma and nondegenerate by
`nondegenerate_toBilin'_iff_det_ne_zero`. Let `P` be the matrix whose rows are the family
vectors; then `P C Pᵀ = J` entrywise. Since `2 k = card m`, choose `e : Fin k ⊕ Fin k ≃ m`.
The square matrix `P₁ = P ∘ e` satisfies `P₁ C' P₁ᵀ = J` (`C'` is `C` reindexed). Since
`det J` is a unit, `det P₁ ≠ 0`. Then `P' = P₁⁻¹` reindexed by `e⁻¹` is a two-sided inverse
of `P`.

`mul_mul_mem_symplecticGroup_iff` is a direct computation:
`(P g P') J (P g P')ᵀ = P (g C gᵀ) Pᵀ`, and `X ↦ P X Pᵀ` is injective because `P' P = 1`.

## Provenance

The Darboux theorem is standard. Neither Mathlib nor the Library has it. The proof here is
the usual induction by splitting off hyperbolic planes, written with Mathlib's
orthogonal-complement API for bilinear forms. It avoids `1/2`, so it covers characteristic 2.
