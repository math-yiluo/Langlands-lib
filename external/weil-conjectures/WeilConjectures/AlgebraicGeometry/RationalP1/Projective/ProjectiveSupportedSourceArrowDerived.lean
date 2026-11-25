/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Projective.ProjectiveDiagonalComposition
public import WeilConjectures.AlgebraicGeometry.RationalP1.Second.RationalP1SecondPullComparison
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientCategory
import WeilConjectures.AlgebraicGeometry.RationalP1.Projective.ProjectivePullSectionSingle
import WeilConjectures.AlgebraicGeometry.RationalP1.Projective.ProjectiveSupportedNormalization
import WeilConjectures.AlgebraicGeometry.RationalP1.Projective.ProjectiveSectionSingle
import WeilConjectures.AlgebraicGeometry.RationalP1.Projective.ProjectiveDiagramSingle
import WeilConjectures.AlgebraicGeometry.RationalP1.Projective.ProjectiveResidualTarget

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Post-normalization comparison for the supported source.

This is the residual compatibility between the canonical derived unit and the
conjugate section comparison. It is strictly smaller than the final statement
because it omits the support normalization isomorphism.
-/
theorem supported_source_arrow_derived_core
    (Y : Scheme.{u}) (L : ∀ X : Scheme.{u}, Modules Λ X)
    (d : Diagram Λ Y L) :
    diagonalTraceRightSingle
          (CondensedRing.lowerStar Λ (secondProjection Y)) d.R₂
          (source Λ Y) ≫
        (secondDiagramPushIso Λ Y L d).hom.app
          ((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
            (source Λ Y)) =
      (DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).map d.support₂.iso.inv ≫
        (pushSectionIso Λ Y).hom.app (unit Λ (ProjectiveLine Y)) ≫
        (moduleObjectDerivedPushforward Λ (secondProjection Y)).map
          (supportedUnitIso Λ Y).hom := by
  rw [projective_diagram_single Λ Y L d]
  exact projective_residual_target Λ Y L d

/-- Derived-unit evaluation of the supported source.
-/
theorem supported_source_arrow_derived
    (Y : Scheme.{u}) (L : ∀ X : Scheme.{u}, Modules Λ X)
    (d : Diagram Λ Y L) :
    (DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).map d.support₂.iso.hom ≫
        diagonalTraceRightSingle
          (CondensedRing.lowerStar Λ (secondProjection Y)) d.R₂
          (source Λ Y) ≫
        (secondDiagramPushIso Λ Y L d).hom.app
          ((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
            (source Λ Y)) =
      (pushSectionIso Λ Y).hom.app (unit Λ (ProjectiveLine Y)) ≫
        (moduleObjectDerivedPushforward Λ (secondProjection Y)).map
          (supportedUnitIso Λ Y).hom := by
  rw [supported_source_arrow_derived_core Λ Y L d]
  rw [← Category.assoc]
  rw [← (DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).map_comp]
  rw [Iso.hom_inv_id]
  simp

end AlgebraicGeometry.ProEtale.RationalP1
