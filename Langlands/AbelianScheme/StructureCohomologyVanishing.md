# Vanishing of structure-sheaf cohomology of an abelian variety above its dimension

Module `Langlands.AbelianScheme.StructureCohomologyVanishing`, namespace
`Langlands.AbelianScheme`.

Author: Worker 5218.

## Purpose

Task 6105 (`FieldH2ExteriorCoproductComparisonStatement`) uses a bounded
creation-contraction family on `H*(A, 𝒪_A)`. Its bound hypothesis is
`∀ n, dim H¹(A, 𝒪_A) < n → Hⁿ(A, 𝒪_A) = 0`. This module proves the geometric
vanishing above the relative dimension `g`. It also reduces the bound above
`dim H¹` to the single inequality `g ≤ dim H¹(A, 𝒪_A)` for a chosen relative
dimension `g = fieldRelativeDimension A`.

This module does not prove that inequality. It is the reverse half of the
unproved published statement `FieldStructureSheafH1DimensionStatement`
(Task 6458). The Library already proves the upper bound `dim H¹ ≤ g`
(`FieldStructureSheafH1DimensionBoundStatement`).

## Notation

`K` is a field and `A : AbelianScheme (Spec (CommRingCat.of K))`. Write
`Hⁿ(A, 𝒪_A)` for
`(DerivedSections.relativeCohomology A.X.hom n).obj (SheafOfModules.unit A.X.left.ringCatSheaf)`.
This is the actual right-derived cohomology of the target statement. It is
definitionally `structureCohomology A.X n` of
`Langlands.AbelianScheme.StructureCohomologyKunnethDimension`. It is also the
module `(relativeCohomology A.X.hom n).obj (structureSheaf A.X.left)` of
`FieldStructureSheafH1DimensionStatement`, since
`Langlands.Scheme.Modules.structureSheaf X` is defined as
`SheafOfModules.unit X.ringCatSheaf`.

## Results

- `exists_hasRelativeDimension_of_field A : ∃ g, A.HasRelativeDimension g`.
  `A.X.left` is connected
  (`GeometricallyConnected.connectedSpace_of_subsingleton`, as `Spec K` is a
  point). The published `smoothConnectedRelativeDimension` gives one
  relative dimension of the smooth morphism `A.X.hom`.
- `isZero_structureCohomology_of_lt A hg hn`: if `A.HasRelativeDimension g`
  and `g < n`, then `Hⁿ(A, 𝒪_A)` is a zero object.
  `A.X.left` is quasi-compact (`QuasiCompact.compactSpace_of_compactSpace`) and
  locally noetherian (`LocallyOfFiniteType.isLocallyNoetherian`), so it is
  noetherian. It is separated, because `terminal.from A.X.left` factors as
  `A.X.hom` followed by the separated map from the affine scheme `Spec K`. The
  published `fieldSmoothTopologicalKrullDim` gives
  `topologicalKrullDim A.X.left ≤ g`. The published
  `noetherianSeparatedQuasicoherentVanishing` then gives the claim for
  `d = g`, applied to the quasi-coherent structure sheaf
  (`CechDegreeOne.isQuasicoherent_unit`). This is the argument of the
  Library's `vanishing_of` (module
  `FieldStructureSheafH1DimensionBoundCech`), which is stated only for
  `n = g + 1`. Here every `n > g` is allowed.
- `subsingleton_structureCohomology_of_lt`: the same conclusion as
  `Subsingleton`, via `ModuleCat.isZero_iff_subsingleton`.
- `fieldRelativeDimension A : ℕ` (definition): a relative dimension of `A`,
  chosen by `Classical.choose` from `exists_hasRelativeDimension_of_field A`.
  `hasRelativeDimension_fieldRelativeDimension` records
  `A.HasRelativeDimension (fieldRelativeDimension A)`. Uniqueness of the
  relative dimension is not needed and not proved.
- `subsingleton_structureCohomology_of_fieldRelativeDimension_lt`:
  `Hⁿ(A, 𝒪_A)` is subsingleton for every `n > fieldRelativeDimension A`.
- `subsingleton_structureCohomology_of_finrank_lt A hlow n hn`: assume
  `hlow : fieldRelativeDimension A ≤ finrank K H¹(A, 𝒪_A)`. Then
  `finrank K H¹(A, 𝒪_A) < n` implies `Subsingleton Hⁿ(A, 𝒪_A)`, since
  `fieldRelativeDimension A < n`.
- `subsingleton_structureCohomology_of_finrank_lt_of_H1Dimension A h n hn`:
  the same conclusion, where `hlow` is the equality of
  `h : FieldStructureSheafH1DimensionStatement.{u}` for
  `g = fieldRelativeDimension A`. That statement is a
  hypothesis here, not a proved input.

## Dependencies and exclusions

The proofs use only these published Library proofs:
`smoothConnectedRelativeDimension`, `fieldSmoothTopologicalKrullDim`,
`noetherianSeparatedQuasicoherentVanishing` and
`CechDegreeOne.isQuasicoherent_unit`. These are general results on smooth
schemes and on noetherian schemes. The import closure of this module (70
Library modules) contains none of the modules of the six Picard and
dual-scheme statements excluded by Task 6105, and no module of
`FieldH2PrimitiveInjectivityStatement` or its proofs.

## Provenance

This is derived internal infrastructure. It instantiates the Library's
published vanishing theorem above the topological dimension of a noetherian
separated scheme, a form of Grothendieck's vanishing theorem. No new source
is formalized. The remaining results only choose a relative dimension and
rearrange inequalities.
