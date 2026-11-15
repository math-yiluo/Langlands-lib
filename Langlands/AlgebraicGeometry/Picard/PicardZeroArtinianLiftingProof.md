# Proof: Artinian lifting of Picard-zero families on abelian schemes

Module `Langlands.AlgebraicGeometry.Picard.PicardZeroArtinianLiftingProof`.
Authors: Worker 225 and Worker 3612 (helper modules and conditional assembly, carried
draft of Task 5640), and Worker 5640 (final assembly, Task 5640).

## Statement proved

The theorem `Langlands.AbelianScheme.picardZeroArtinianLifting` proves the published
proposition `Langlands.AbelianScheme.PicardZeroArtinianLiftingStatement.{u}` exactly, with
no hypotheses. That proposition is in module
`Langlands.AlgebraicGeometry.Picard.PicardZeroArtinianLiftingStatement`.

The proposition says the following. Let `A` be an abelian scheme over a scheme `S`. Let
`φ : B' → B` be a surjection of local Artinian rings in `Type u` with
`maximalIdeal B' * ker φ = ⊥`, and let `β : Spec B' ⟶ S`. Let `M` be a rigidified family
on `A` over `Spec B` (viewed over `S` through `Spec φ ≫ β`) that is geometrically
Picard-zero (`IsPicardZeroFamily`). Then there is a geometrically Picard-zero rigidified
family `M'` on `A` over `Spec B'` whose rigidified pullback along `Spec φ` is isomorphic
to `M`.

## Declarations

- `Langlands.AbelianScheme.picardZeroArtinianLifting_of_artinianPrimitive (hP) :
  PicardZeroArtinianLiftingStatement`, where
  `hP : ArtinianPrimitiveLineBundleLiftingStatement`. This is the conditional form. It
  derives the target from the lifting of primitive line bundles
  (`m^*L ≅ p₁^*L ⊗ p₂^*L`) along a surjection `φ : B' → B` of local Artinian rings with
  `maximalIdeal B' * ker φ = ⊥`.
- `Langlands.AbelianScheme.picardZeroArtinianLifting : PicardZeroArtinianLiftingStatement`.
  This is the unconditional proof of the target.

## Implemented proof

1. `picardZeroArtinianLifting_of_artinianPrimitive hP` is the term
   `PicardZeroArtinianLiftingReduction.picardZeroArtinianLifting_of_primitive hP hQ`
   (module [`PicardZeroArtinianPrimitiveTransport`](PicardZeroArtinianPrimitiveTransport.md),
   which builds on [`PicardZeroArtinianLiftingReduction`](PicardZeroArtinianLiftingReduction.md)).
   Here `hQ` is `fun B _ _ _ X L hL ↦ OnePointSquare.artinianLocalSquare B X L hL`
   (module [`OnePointPicardZeroSquare`](OnePointPicardZeroSquare.md)). This is the theorem
   of the square for geometrically Picard-zero line bundles over the spectrum of a local
   Artinian ring: such a bundle `L` satisfies `m^*L ≅ p₁^*L ⊗ p₂^*L`. The conclusion of
   `artinianLocalSquare` is the body of the definition `IsPrimitiveLineBundle X L`, so the
   term closes by definitional unfolding.
2. `picardZeroArtinianLifting` applies the conditional form to the published proof
   `Langlands.AbelianScheme.artinianPrimitiveLineBundleLifting :
   ArtinianPrimitiveLineBundleLiftingStatement.{u}` (module
   [`ArtinianPrimitiveLineBundleLiftingProof`](ArtinianPrimitiveLineBundleLiftingProof.md),
   Task 5704). Both are in the same universe `u`.

## Constraint check

The task forbids using `FiniteTypeDualSchemeGeometryStatement`,
`RelativeDualSchemeGeometryStatement`,
`FiniteTypeSmoothFamilyAbelianRepresentabilityStatement` and
`SmoothFamilyAbelianRepresentabilityStatement`, their proofs, or any result routed through
them. A scan of the source of all 2,106 `Langlands` modules in the import closure of this
module at Library commit `aeb3911c` found no occurrence of `DualSchemeGeometry` or
`SmoothFamilyAbelianRepresentability`. `PicardZeroArtinianLifting` occurs only in the
target statement module and in the four modules of this proof.

## Provenance

The target is a derived formulation of the Artinian case of Faltings–Chai, *Degeneration
of Abelian Varieties*, Chapter I, Remark 1.5(c); see the Markdown of
`PicardZeroArtinianLiftingStatement`. The split into the reduction, the theorem of the
square over a one-point base and the lifting of primitive bundles is internal to Task 5640
(`d1735ac9-6af5-4460-8c3a-b09a43c01ffa`). The lifting of primitive bundles is the
obstruction-vanishing step in the proof of Proposition 6.7 of Mumford–Fogarty–Kirwan,
*Geometric Invariant Theory*, 3rd ed.; see the Markdown of
`ArtinianPrimitiveLineBundleLiftingProof`.
