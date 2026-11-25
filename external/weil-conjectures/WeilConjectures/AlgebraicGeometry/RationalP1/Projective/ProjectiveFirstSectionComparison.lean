/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Ambient.RationalP1AmbientComposites
public import WeilConjectures.AlgebraicGeometry.RationalP1.Projective.ProjectiveSectionSingle

/-! # Canonical first-projection section and path comparisons -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

attribute [local irreducible] moduleObjectDerivedPushforward moduleObjectDerivedPullback
attribute [local irreducible] firstProjection secondProjection square
attribute [local irreducible] projectionMap singleUnitIso

/-- Change the second direct-image path to the first by conjugating the canonical
pullback comparison. -/
@[irreducible]
def firstPathComparison
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u}) :
    moduleObjectDerivedPushforward Λ (secondProjection Y) ⋙
        moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y) ≅
      moduleObjectDerivedPushforward Λ (firstProjection Y) ⋙
        moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y) := by
  unfold moduleObjectDerivedPushforward
  exact (conjugateIsoEquiv
    ((CondensedRing.derivedUpperStarLowerStarAdjunction Λ (ProjectiveLine Y ↘ Y)).comp
      (CondensedRing.derivedUpperStarLowerStarAdjunction Λ (firstProjection Y)))
    ((CondensedRing.derivedUpperStarLowerStarAdjunction Λ (ProjectiveLine Y ↘ Y)).comp
      (CondensedRing.derivedUpperStarLowerStarAdjunction Λ (secondProjection Y)))
    (condensedAmbientPullbackComparison Λ (square Y))).symm

/-- The canonical section comparison for the first projection, obtained by conjugating
its pullback section comparison. -/
@[irreducible]
def firstPushSectionIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u}) :
    𝟭 (DerivedCategory (Modules Λ (ProjectiveLine Y))) ≅
      moduleObjectDerivedPushforward Λ (diagonalImmersion Y) ⋙
        moduleObjectDerivedPushforward Λ (firstProjection Y) := by
  unfold moduleObjectDerivedPushforward
  exact conjugateIsoEquiv Adjunction.id
    ((CondensedRing.derivedUpperStarLowerStarAdjunction Λ (firstProjection Y)).comp
      (CondensedRing.derivedUpperStarLowerStarAdjunction Λ (diagonalImmersion Y)))
    (derivedSection Λ Y (firstProjection Y)
      (by unfold firstProjection; exact pullback.diagonal_fst _))

/-- Realize the diagram's canonical first direct image in the fixed native interface. -/
@[irreducible]
def firstDiagramPushIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules Λ X) (d : Diagram Λ Y L) :
    d.R₁.R ≅ moduleObjectDerivedPushforward Λ (firstProjection Y) :=
  eqToIso (show d.R₁.R = moduleObjectDerivedPushforward Λ (firstProjection Y) from by
    unfold moduleObjectDerivedPushforward firstProjection
    exact d.p₁_canonical)

end AlgebraicGeometry.ProEtale.RationalP1
