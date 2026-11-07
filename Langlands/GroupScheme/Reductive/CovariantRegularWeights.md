# Torus weights of actual covariant regular representations

This internal comparison works over any field `k : Type u`, with arbitrary
characteristic, for an actual affine group scheme `G` and a supplied split
pinning `p`. Let `V` be a finite-dimensional subspace of the actual coordinate
algebra of `G`, with a basis `b`, stable under all coalgebra right translations.
Suppose every element of `V` is left covariant under the negative Borel with
the coordinate of the torus character `lam`. For the actual finite regular
representation on `V`, every occurring torus weight `mu` then satisfies
`lam - mu ∈ p.positiveRootMonoid`.

## Evaluation and coordinate comparisons

`MatrixRepresentation.characterSpace_points` transports the universal affine
character-vector equation to every original relative scheme test. It first
uses the canonical global-section equivalence on the universal affine point,
then pulls the equation back along the point under consideration. Naturality
of matrices, characters and scalar extension preserves this equation.
`characterEval_eq_section_characterValue` compares global-section character
evaluation with the actual affine-algebra character value.

The coordinate interfaces `AffineCoordinates.algebra` and
`CharacterUnits.Coord` choose different affine presentations. The algebra
isomorphism `AffineCoordinates.lieCoordinateEquiv` is obtained by applying the
fully faithful spectrum functor to the two coordinate isomorphisms of the
same actual group. Its point and evaluation lemmas show that this comparison
preserves each supplied actual affine point. No definitional equality of the
two presentations is assumed.

For the coordinate function represented by a vector in `V`,
`Chevalley.pointAlgebraHom_affineRegularCoordinateMap_mul_of_character`
converts an actual character vector into a right-character equation on all
scheme tests. It uses the existing multiplication formula for the regular
representation and sums the resulting scalar eigenvector equation.
`SplitPinning.pointAlgebraHom_leftTorus_of_covariant` restricts left Borel
covariance to the torus and identifies its character as `lam`.

## Actual restriction and its weight

`SplitPinning.covariantRegularRestriction` sends a vector to its coordinate
function, pulls it back along the actual positive-unipotent inclusion, and
transports it through `lieCoordinateEquiv`. The existing product-cell
restriction theorem makes this map injective on a left-covariant subspace.
Its evaluation lemma gives evaluation of the original coordinate at the
included subgroup point.

`covariantRegularRestriction_mem_weightSpace` proves that a vector of torus
weight `mu` restricts to an eigenfunction of the conjugation action on the
positive unipotent subgroup with character `lam - mu`. Indeed, evaluation at
`t u t⁻¹` equals `lam(t) mu(t)⁻¹` times evaluation at `u`, by left covariance
and the right-character equation. The comparison of character conventions
makes this exactly the published all-algebra coordinate-weight equation.
Injectivity makes the restricted function nonzero when the vector is
nonzero. The published coordinate-weight theorem for the positive-unipotent
action then proves `affineRegularRepresentation_weight_le`.

## Provenance and scope

These are internal consequences of the imported universal character spaces,
actual affine presentations, regular representation, and published
`SplitBorelCellAction` and `CovariantCellRestriction` results. The proof uses
no additional structural or existence hypothesis. It does not construct a
normalized covariant coordinate or establish that `lam` occurs, its
multiplicity, or unconditional fundamental-representation existence.
