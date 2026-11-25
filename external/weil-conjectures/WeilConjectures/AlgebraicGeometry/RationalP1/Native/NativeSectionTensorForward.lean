/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Projective.ProjectiveFirstSectionComparison
import WeilConjectures.AlgebraicGeometry.RationalP1.Projective.ProjectiveFirstKernelEvaluation
import WeilConjectures.AlgebraicGeometry.RationalP1.First.FirstDiagramCoefficientTransport

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
attribute [local implicit_reducible] firstProjection
attribute [local irreducible] secondProjection square
attribute [local irreducible] projectionMap singleUnitIso
attribute [local irreducible] CategoryTheory.Sheaf.monoidalCategory
  CategoryTheory.Mod.monoidalCategory CategoryTheory.Mod.monoidalClosed
  DerivedCategory.monoidalClosed
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

/-- Evaluate the native kernel prefix with an arbitrary condensed coefficient ring. -/
theorem native_section_tensor_forward
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules Λ X)
    (d : Diagram Λ Y L)
    (M : DerivedCategory (Modules Λ (ProjectiveLine Y)))
    (N : DerivedCategory (Modules Λ (diagonalSurface Y)))
    (α : (DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
      (source Λ Y) ⟶ N)
    (hobj : d.R₁.R.obj N =
      (moduleObjectDerivedPushforward Λ (firstProjection Y)).obj N)
    :
    (firstPushSectionIso Λ Y).hom.app M ≫
      (moduleObjectDerivedPushforward Λ (firstProjection Y)).map
        ((diagonalTensorIso Λ Y M).hom ≫
          ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M ◁
            ((supportedUnitIso Λ Y).hom ≫ α))) =
    (ρ_ M).inv ≫
      (M ◁ ((singleUnitIso Λ (ProjectiveLine Y)).inv ≫
        d.support₁.hom ≫ d.R₁.R.map α ≫
        (eqToIso d.p₁_canonical).hom.app N ≫
        eqToHom ((congrArg (fun F => F.obj N) d.p₁_canonical).symm.trans hobj))) ≫
      projectionMap Λ (firstProjection Y) M N := by
  let : MonoidalCategory (DerivedCategory (Modules Λ (ProjectiveLine Y))) :=
    internalMonoidal Λ (ProjectiveLine Y)
  let : MonoidalCategory (DerivedCategory (Modules Λ (diagonalSurface Y))) :=
    internalMonoidal Λ (diagonalSurface Y)
  have ha :
      ((singleUnitIso Λ (ProjectiveLine Y)).inv ≫ d.support₁.hom ≫
        (firstDiagramPushIso Λ Y L d).hom.app
          ((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
            (source Λ Y))) ≫
          (moduleObjectDerivedPushforward Λ (firstProjection Y)).map α =
      (singleUnitIso Λ (ProjectiveLine Y)).inv ≫ d.support₁.hom ≫ d.R₁.R.map α ≫
        (eqToIso d.p₁_canonical).hom.app N ≫
          eqToHom ((congrArg (fun F ↦ F.obj N) d.p₁_canonical).symm.trans hobj) := by
    simp only [Category.assoc]
    rw [first_diagram_coefficient_transport Λ Y L d α hobj]
  have hf := first_supported_kernel_forward Λ Y L d M N α
  rw [ha] at hf
  exact hf

end AlgebraicGeometry.ProEtale.RationalP1
