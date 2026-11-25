/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Projective.ProjectiveFirstSectionComparison
import WeilConjectures.AlgebraicGeometry.RationalP1.Projective.ProjectiveFirstSupportedProjection
import WeilConjectures.AlgebraicGeometry.RationalP1.Projective.ProjectiveProjectionNaturalityRight

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

attribute [local implicit_reducible] moduleObjectDerivedPushforward moduleObjectDerivedPullback
attribute [local irreducible] firstProjection secondProjection square
attribute [local irreducible] projectionMap singleUnitIso

/-- Forward section evaluation after inserting a coefficient arrow. -/
theorem first_supported_kernel_forward
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules Λ X) (d : Diagram Λ Y L)
    (M : DerivedCategory (Modules Λ (ProjectiveLine Y)))
    (N : DerivedCategory (Modules Λ (diagonalSurface Y)))
    (α : (DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
      (source Λ Y) ⟶ N) :
    (firstPushSectionIso Λ Y).hom.app M ≫
      (moduleObjectDerivedPushforward Λ (firstProjection Y)).map
        ((diagonalTensorIso Λ Y M).hom ≫
          ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M ◁
            ((supportedUnitIso Λ Y).hom ≫ α))) =
    (ρ_ M).inv ≫
      (M ◁ (((singleUnitIso Λ (ProjectiveLine Y)).inv ≫ d.support₁.hom ≫
        (firstDiagramPushIso Λ Y L d).hom.app
          ((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
            (source Λ Y))) ≫
              (moduleObjectDerivedPushforward Λ (firstProjection Y)).map α)) ≫
      projectionMap Λ (firstProjection Y) M N := by
  let : MonoidalCategory (DerivedCategory (Modules Λ (ProjectiveLine Y))) :=
    internalMonoidal Λ (ProjectiveLine Y)
  let : MonoidalCategory (DerivedCategory (Modules Λ (diagonalSurface Y))) :=
    internalMonoidal Λ (diagonalSurface Y)
  let R := moduleObjectDerivedPushforward Λ (firstProjection Y)
  have hs := first_supported_projection Λ Y L d M
  have hn := projectionMap_naturality_right Λ (firstProjection Y) M α
  rw [MonoidalCategory.whiskerLeft_comp,
    ← Category.assoc (diagonalTensorIso Λ Y M).hom,
    R.map_comp, ← Category.assoc, hs]
  simp only [Category.assoc]
  rw [← hn, ← MonoidalCategory.whiskerLeft_comp_assoc]
  simp only [Category.assoc]

end AlgebraicGeometry.ProEtale.RationalP1
