/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Projective.ProjectiveSupportedSourceArrow

/-! # Normalization of the supported coefficient source -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The normalized diagram source arrow is the canonical supported-unit arrow. -/
theorem supported_source_normalization
    (Y : Scheme.{u}) (L : ∀ X : Scheme.{u}, Modules Λ X)
    (d : Diagram Λ Y L)
    (M : DerivedCategory (Modules Λ (ProjectiveLine Y))) :
    (M ◁ ((singleUnitIso Λ (ProjectiveLine Y)).inv ≫ d.support₂.hom ≫
      (secondDiagramPushIso Λ Y L d).hom.app
        ((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
          (source Λ Y)))) =
    (M ◁ ((singleUnitIso Λ (ProjectiveLine Y)).inv ≫
      (pushSectionIso Λ Y).hom.app (unit Λ (ProjectiveLine Y)) ≫
      (moduleObjectDerivedPushforward Λ (secondProjection Y)).map
        (supportedUnitIso Λ Y).hom)) := by
  have h := supported_source_arrow Λ Y L d
  simpa only [Category.assoc] using congrArg
    (fun z ↦ M ◁ ((singleUnitIso Λ (ProjectiveLine Y)).inv ≫ z)) h

end AlgebraicGeometry.ProEtale.RationalP1
