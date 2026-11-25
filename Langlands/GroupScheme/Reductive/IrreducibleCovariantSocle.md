# Every irreducible representation is a covariant socle

`SplitPinning.exists_isRealizedBy_intertwines_affineCovariantSocleRepresentation`:
let `p` be a split pinning of `G` over a field `k`, and let
`ρ : MatrixRepresentation G n` be irreducible. Then there are:

- a torus character `lam`;
- a coordinate `f` with `p.IsRealizedBy lam f` (module `Reductive.SplitBorelCell`);
- a matrix `C` with `ρ.Intertwines (Chevalley.affineCovariantSocleRepresentation G f) C`
  and `C.mulVecLin` bijective.

So every simple representation is isomorphic to the covariant socle representation
of a realizing coordinate (module `Reductive.CovariantSocleIrreducible`). That socle
is the regular span `Chevalley.affineCovariantSocle G f` of `f`, with its chosen
basis.

## Proof

1. `n` is nonempty, since `kⁿ` is nontrivial by irreducibility.
2. `SplitPinning.exists_negativeBorel_eigenCovector` (module
   `Reductive.NegativeBorelEigenCovector`) gives `ξ ≠ 0` and `lam` such that the
   negative Borel subgroup acts on `ξ` by the character coordinate of `lam`.
3. `Chevalley.exists_affineRegular_bijective_matrixCoefficient` (module
   `Reductive.CovectorRegularEmbedding`) gives a finite right-stable subspace `V` with
   basis `b` and a bijective intertwiner `C` from `ρ` to
   `affineRegularRepresentation G V b hV`. Under `C`, coordinate functions are the
   matrix coefficients of `ξ`.
4. `V` is left covariant: `V ≤ leftCovariantSubspace p.negativeBorelHom
   (p.borelCharacterCoordinate lam)`. Every `w ∈ V` is the coordinate function of its
   basis coordinates. These coordinates are `C *ᵥ v` for some `v`, by surjectivity of
   `C`. So `w` is the matrix coefficient of `ξ` and `v`, which is left covariant by
   `matrixCoefficient_mem_leftCovariantSubspace`.
5. `V ≠ ⊥`. Otherwise every basis vector would vanish, so `Fin d` would be empty and
   `C` could not be injective on the nonzero space `kⁿ`.
6. `Chevalley.affineRegularRepresentation_exists_normalized_fixedVector` (module
   `Reductive.CovariantUnipotentFixedLine`) gives a vector `v₀` fixed by the
   positive unipotent subgroup whose coordinate function has counit one. Its inputs
   are the unipotence of the positive unipotent subgroup and the cell coordinate
   `p.cellCoordinate` with its factorization `p.exists_factors_of_isUnit_cellCoordinate`.
   Let `f` be the coordinate function of `v₀`. It is left covariant by step 4, right
   invariant by `affineRegularCoordinateMap_mem_rightInvariant_of_fixedVector`, and
   has counit one. So `p.IsRealizedBy lam f`.
7. `Chevalley.affineCovariantSocle_le_of_nonzero_rightAct_mem` (module
   `Reductive.CovariantSocle`) gives `affineCovariantSocle G f ≤ V`.
8. The coordinates `D` of the socle basis in the basis `b` intertwine the socle
   representation with the regular representation on `V`
   (`intertwines_affine_coactionCoordinates`, module
   `Reductive.CovariantTensorEmbedding`). `D` is injective
   (`coactionCoordinates_mulVecLin_injective`). The regular representation on `V` is
   irreducible, being isomorphic to `ρ` (`Intertwines.isIrreducible_of_bijective`).
   The range of `D` is stable (`Intertwines.isStableSubspace_range`). It is nonzero
   because the socle is nonzero (`affineCovariantSocle_ne_bot`) and `D` is
   injective. So the range is everything and `D` is bijective.
9. `Intertwines.exists_inverse` (module `Rational.HighestWeightIntertwiners`) gives a
   bijective intertwiner `E` from the regular representation on `V` to the socle
   representation. The required matrix is `E * C`. It intertwines by
   `Intertwines.comp`, and it is bijective as a composite of bijections
   (`Matrix.mulVecLin_mul`).

## Provenance

This is internal. It plays the role of the statement in Milne, *Algebraic Groups*
(2017, registered as `milne-2017-algebraic-groups`), Theorem 22.2, that every simple
representation is a `V(λ)`. Instead of primitive vectors, it uses an eigen-covector
for the opposite Borel subgroup, matrix coefficients, and the Library's
covariant-socle construction.
