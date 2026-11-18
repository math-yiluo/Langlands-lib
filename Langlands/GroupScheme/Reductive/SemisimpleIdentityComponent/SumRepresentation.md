# The direct sum of two matrix representations on `Fin (n + m)`

This module is internal supporting work for the proof of
`Langlands.GroupScheme.CharZeroSemisimpleRepresentationIdentityComponentStatement`. It constructs
the direct sum of two matrix representations as a matrix representation indexed by
`Fin (n + m)`, so that it can serve as a faithful representation in Milne's Theorem 22.42 (stated
for index types `Fin N`), and proves that the direct sum of two representations with semisimple
rational-point representations has semisimple rational-point representation.

## Block matrices

For matrices `M : Matrix (Fin n) (Fin n) A` and `N : Matrix (Fin m) (Fin m) A`,
`sumMatrix M N` is Mathlib's block matrix `Matrix.fromBlocks M 0 0 N`, reindexed along
`finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m)`. The lemmas `sumMatrix_one`, `sumMatrix_mul`,
`sumMatrix_map` (entrywise ring maps) and `sumMatrix_eq_one_iff` (`sumMatrix M N = 1 ↔ M = 1 ∧
N = 1`) are proved from Mathlib's block-matrix lemmas. `sumInl v` and `sumInr w` place vectors
into the two blocks; `sumMatrix_mulVec_sumInl`, `sumMatrix_mulVec_sumInr` and
`sumInl_add_sumInr` describe the action and the decomposition of every vector.

## The direct-sum representation

For `ρ : MatrixRepresentation G (Fin n)` and `σ : MatrixRepresentation G (Fin m)` over any
commutative ring `R`:

- `sumMatrixHom ρ σ T` is the monoid homomorphism `x ↦ sumMatrix (ρ(x)) (σ(x))` on points over
  the test scheme `T`, and `sumPoints ρ σ T` the corresponding general-linear points;
  `sumPoints_naturality` proves naturality in `T`.
- `MatrixRepresentation.sum ρ σ : MatrixRepresentation G (Fin (n + m))` is the group-scheme
  homomorphism given by the published `homOfPoints`.
- `sum_pointMatrix_val` gives its point matrices, `sum_pointMatrix_eq_one_iff` says a point is in
  its kernel exactly when it is in both kernels, and `sum_rationalMatrix_val` gives its rational
  matrices.

This follows the published `MatrixRepresentation.directSum` (finite families indexed by sigma
types), specialized to two summands and to the index `Fin (n + m)`.

## Semisimplicity

- `isSemisimpleRepresentation_of_sup_range`: for representations `τ`, `τ₁`, `τ₂` of a group over
  a field and intertwining maps `f₁ : τ₁ → τ`, `f₂ : τ₂ → τ` whose ranges span, if `τ₁` and `τ₂`
  are semisimple then so is `τ`. Through Mathlib's `equivLinearMapAsModule` the ranges are
  `k[Γ]`-submodules of `τ.asModule` that are semisimple (`IsSemisimpleModule.range`), and their
  supremum is semisimple (`IsSemisimpleModule.sup`).
- `sum_rationalRepresentation_isSemisimple`: over a field, if `ρ.rationalRepresentation` and
  `σ.rationalRepresentation` are semisimple, so is `(ρ.sum σ).rationalRepresentation`; the maps
  `sumInl` and `sumInr` are the intertwining maps.

## Provenance

Internal. A standard construction (direct sum of representations) and a standard fact (a sum of
semisimple modules is semisimple), formalized on top of the published `homOfPoints` and
Mathlib's representation and semisimple-module theory.
