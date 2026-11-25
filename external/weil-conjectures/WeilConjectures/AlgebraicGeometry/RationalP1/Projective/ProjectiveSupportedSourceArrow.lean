/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Projective.ProjectiveDiagonalComposition
public import WeilConjectures.AlgebraicGeometry.RationalP1.Second.RationalP1SecondPullComparison
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientCategory
import WeilConjectures.AlgebraicGeometry.RationalP1.Projective.ProjectiveSupportedSourceArrowDerived

/-! # Supported source arrow before tensor normalization -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The supported diagram arrow is the canonical section-source arrow.
-/
theorem supported_source_arrow
    (Y : Scheme.{u}) (L : ∀ X : Scheme.{u}, Modules Λ X)
    (d : Diagram Λ Y L) :
    d.support₂.hom ≫ (secondDiagramPushIso Λ Y L d).hom.app
        ((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
          (source Λ Y)) =
      (pushSectionIso Λ Y).hom.app (unit Λ (ProjectiveLine Y)) ≫
        (moduleObjectDerivedPushforward Λ (secondProjection Y)).map
          (supportedUnitIso Λ Y).hom := by
  dsimp only [DiagonalTrace.NormalizedSource.hom]
  simpa only [DiagonalCoefficients.Modules, secondProjection, Category.assoc] using
    supported_source_arrow_derived Λ Y L d

end AlgebraicGeometry.ProEtale.RationalP1
