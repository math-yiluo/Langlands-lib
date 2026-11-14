# The first structure-sheaf cohomology of an abelian variety has dimension `g`

Author: Worker 372.

This module proves the published proposition
`Langlands.AbelianScheme.FieldStructureSheafH1DimensionStatement`. The theorem is
`Langlands.AbelianScheme.fieldStructureSheafH1Dimension`. Let `k` be any field, `A` an abelian
scheme over `Spec k`, and `g` a number with `A.HasRelativeDimension g`. Then the `k`-module
`H = (DerivedSections.relativeCohomology A.X.hom 1).obj (structureSheaf A.X.left)` is
finite-dimensional and `Module.finrank k H = g`.

It contains no `sorry` and no new axioms. Its axioms are `propext`, `Classical.choice` and
`Quot.sound`.

## Proof

The theorem combines two inequalities.

- **Upper bound.** The published Library theorem
  `Langlands.AbelianScheme.fieldStructureSheafH1DimensionBound` (module
  `Langlands.AbelianScheme.FieldStructureSheafH1DimensionBoundProof`) gives finite dimension and
  `finrank k H ≤ g`.
- **Lower bound.** `Langlands.AbelianScheme.FieldH1LowerBound.le_finrank` gives
  `g ≤ finrank k H`.

`le_antisymm` gives the equality.

The lower bound is proved in these new helper modules, in reading order:

1. `Langlands.RingTheory.LocalGeneratorsKrullDimension`: Nakayama and Krull's height theorem
   bound `ringKrullDim` of a Noetherian local ring by the number of elements of `𝔪` that span
   `𝔪^c` modulo `𝔪^{c+1}`.
2. `Langlands.AlgebraicGeometry.ArtinianLocusStalk`: a local point at `x` that factors through
   a locally Artinian closed subscheme kills a fixed power of the maximal ideal at `x`.
3. `Langlands.AlgebraicGeometry.Picard.FieldMinimalPicardHull`: over a field, a formally versal
   hull of the Picard deformation problem whose ring has one generator per basis vector of the
   first-order classes. A map from the hull that kills the generators is constant.
4. `Langlands.AbelianScheme.FieldMumfordFiniteLocus`: a relative Picard class on the parameter
   space `A` (the Mumford family of an ample bundle), zero at the unit, whose zero locus is a
   closed subscheme finite over `k`.
5. `Langlands.AbelianScheme.FieldH1LowerBound`: these results, applied at the unit point, give
   `dim 𝒪_{A,0} ≤ finrank` of the first-order classes. The left side is `g` (smoothness at a
   closed point) and the right side is `finrank k H` (first-order classes are `H¹`).

Each helper module's Markdown gives the details.

## Independence from the excluded statements

The task forbids the Picard and dual-scheme representability statements
`ArtinianPrimitiveLineBundleLiftingStatement`, `PicardZeroArtinianLiftingStatement`,
`FiniteTypeDualSchemeGeometryStatement`, `RelativeDualSchemeGeometryStatement`,
`FiniteTypeSmoothFamilyAbelianRepresentabilityStatement` and
`SmoothFamilyAbelianRepresentabilityStatement`, and any proof of
`FieldH2PrimitiveInjectivityStatement`. No module in the import closure of this module mentions
any of these names. The formal hull is built from the unconditional Library deformation machinery,
and the finiteness of the Mumford locus uses only published proofs: ample existence over a field,
the closed agreement locus, ampleness of pullbacks and tensor products, and finiteness of proper
schemes with ample trivial bundle.

## Provenance

The statement and the classical proof are in Mumford, *Abelian Varieties*, and in Edixhoven, van
der Geer and Moonen, *Abelian Varieties* (registered source
`edixhoven-vandergeer-moonen-abelian-varieties-draft`). There the lower bound comes from the
Picard scheme: its tangent space at the origin is `H¹(A, 𝒪_A)`, and `φ_L` has finite kernel
(Lemma (2.19) of the latter). The Lean lower bound follows the same idea with a formal hull in
place of the Picard scheme. It is described in `Langlands.AbelianScheme.FieldH1LowerBound`.
