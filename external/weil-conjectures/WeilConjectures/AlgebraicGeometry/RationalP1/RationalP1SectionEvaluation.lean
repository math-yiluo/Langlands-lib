/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Ambient.RationalP1AmbientComposites
public import WeilConjectures.AlgebraicGeometry.RationalP1.Tate.RationalTatePullback
public import WeilConjectures.AlgebraicGeometry.RationalP1.First.FirstSectionKernelComposites
import WeilConjectures.AlgebraicGeometry.RationalP1.Native.NativeSectionTensorPrefix
import WeilConjectures.AlgebraicGeometry.RationalP1.FinishTensorEvaluation
import WeilConjectures.AlgebraicGeometry.RationalP1.SectionEvaluationCongruence

/-! # Evaluating an arbitrary kernel on the projective diagonal
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false

set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u u₁ u₂
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

attribute [local irreducible] moduleObjectDerivedPushforward moduleObjectDerivedPullback
attribute [local irreducible] firstProjection secondProjection square
attribute [local irreducible] projectionMap singleUnitIso
attribute [local irreducible] CategoryTheory.Sheaf.monoidalCategory
  CategoryTheory.Mod.monoidalCategory CategoryTheory.Mod.monoidalClosed
  DerivedCategory.monoidalClosed
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

attribute [local irreducible] coefficient line diagram secondLineComparison

-- Compare the fixed native functor and tensor instances by structural congruence.
/-- The kernel-insertion prefix before the terminal first-projection functional.
This is the strict prefix of `first_section_tensor_evaluation_core`, before any
terminal functional. -/
theorem first_section_tensor_evaluation_prefix
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules (coefficient l c).X X)
    (d : Diagram (coefficient l c).X Y L)
    (M : DerivedCategory (Modules (coefficient l c).X (ProjectiveLine Y)))
    (N : DerivedCategory (Modules (coefficient l c).X (diagonalSurface Y)))
    (α : (DerivedCategory.singleFunctor (Modules (coefficient l c).X (diagonalSurface Y)) 0).obj
      (source (coefficient l c).X Y) ⟶ N)
    (hobj : d.R₁.R.obj N =
      (moduleObjectDerivedPushforward (coefficient l c).X (firstProjection Y)).obj N)
    (hp : IsIso (projectionMap (coefficient l c).X (firstProjection Y) M N)) :
    ((moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).map
        (firstKernelInsertion (coefficient l c).X Y M N α) ≫
      (firstPathComparison (coefficient l c).X Y).hom.app
        ((moduleObjectDerivedPullback (coefficient l c).X (firstProjection Y)).obj M ⊗ N)) ≫
      (moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).map
        (@inv _ _ _ _ (projectionMap (coefficient l c).X (firstProjection Y) M N) hp) =
    (moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).map (ρ_ M).inv ≫
      (moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).map
        (M ◁ ((singleUnitIso (coefficient l c).X (ProjectiveLine Y)).inv ≫
          d.support₁.hom ≫ d.R₁.R.map α ≫
          (eqToIso d.p₁_canonical).hom.app N ≫
          eqToHom ((congrArg (fun F => F.obj N) d.p₁_canonical).symm.trans hobj))) := by
  delta firstKernelInsertion
  section_evaluation_exact native_section_tensor_prefix (coefficient l c).X Y L d M N α hobj hp

/-- Cancellation of the first-projection transport before the terminal unitors. -/
theorem first_section_tensor_evaluation_postprefix
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules (coefficient l c).X X)
    (d : Diagram (coefficient l c).X Y L)
    (M : DerivedCategory (Modules (coefficient l c).X (ProjectiveLine Y)))
    (N : DerivedCategory (Modules (coefficient l c).X (diagonalSurface Y)))
    (α : (DerivedCategory.singleFunctor (Modules (coefficient l c).X (diagonalSurface Y)) 0).obj
      (source (coefficient l c).X Y) ⟶ N)
    (t : d.R₁.R.obj N ⟶ unit (coefficient l c).X (ProjectiveLine Y))
    (hobj : d.R₁.R.obj N =
      (moduleObjectDerivedPushforward (coefficient l c).X (firstProjection Y)).obj N) :
    (moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).map (ρ_ M).inv ≫
      (moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).map
        (M ◁ ((singleUnitIso (coefficient l c).X (ProjectiveLine Y)).inv ≫
          d.support₁.hom ≫ d.R₁.R.map α ≫
          (eqToIso d.p₁_canonical).hom.app N ≫
          eqToHom ((congrArg (fun F => F.obj N) d.p₁_canonical).symm.trans hobj))) ≫
      (moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).map
        (M ◁ firstNativeFunctional (coefficient l c).X Y L d N t) =
    (moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).map (ρ_ M).inv ≫
      (moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).map
        (M ◁ ((singleUnitIso (coefficient l c).X (ProjectiveLine Y)).inv ≫
          d.support₁.hom ≫ d.R₁.R.map α ≫ t)) := by
  unfold moduleObjectDerivedPushforward firstProjection at hobj ⊢
  have hcancel : (eqToIso d.p₁_canonical).hom.app N ≫
      eqToHom ((congrArg (fun F ↦ F.obj N) d.p₁_canonical).symm.trans hobj) ≫
      (eqToIso d.p₁_canonical).inv.app N ≫ t = t := by
    simp only [eqToHom_refl, Category.id_comp, Iso.hom_inv_id_app_assoc]
  unfold firstNativeFunctional
  dsimp only [id, moduleObjectDerivedPushforward, firstProjection]
  rw [← Functor.map_comp, ← MonoidalCategory.whiskerLeft_comp]
  simp only [Category.assoc]
  rw [hcancel]

-- Elaborate the native projection and the two canonical direct-image paths.
/-- The section/projection paste before the terminal unitors. -/
theorem first_section_tensor_evaluation_core
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules (coefficient l c).X X)
    (d : Diagram (coefficient l c).X Y L)
    (M : DerivedCategory (Modules (coefficient l c).X (ProjectiveLine Y)))
    (N : DerivedCategory (Modules (coefficient l c).X (diagonalSurface Y)))
    (α : (DerivedCategory.singleFunctor (Modules (coefficient l c).X (diagonalSurface Y)) 0).obj
      (source (coefficient l c).X Y) ⟶ N)
    (t : d.R₁.R.obj N ⟶ unit (coefficient l c).X (ProjectiveLine Y))
    (hp : IsIso (projectionMap (coefficient l c).X (firstProjection Y) M N)) :
    (moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).map
        (firstKernelInsertion (coefficient l c).X Y M N α) ≫
      (firstPathComparison (coefficient l c).X Y).hom.app
        ((moduleObjectDerivedPullback (coefficient l c).X (firstProjection Y)).obj M ⊗ N) ≫
      (moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).map
        (@inv _ _ _ _ (projectionMap (coefficient l c).X (firstProjection Y) M N) hp) ≫
      (moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).map
        (M ◁ firstNativeFunctional (coefficient l c).X Y L d N t) =
    (moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).map (ρ_ M).inv ≫
      (moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).map
        (M ◁ ((singleUnitIso (coefficient l c).X (ProjectiveLine Y)).inv ≫
          d.support₁.hom ≫ d.R₁.R.map α ≫ t)) := by
  have hcanon : d.R₁.R = moduleObjectDerivedPushforward (coefficient l c).X
      (firstProjection Y) := by
    unfold moduleObjectDerivedPushforward firstProjection
    exact d.p₁_canonical
  have hobj : d.R₁.R.obj N =
      (moduleObjectDerivedPushforward (coefficient l c).X (firstProjection Y)).obj N :=
    congrArg (fun F => F.obj N) hcanon
  rw [← Category.assoc, ← Category.assoc]
  rw [first_section_tensor_evaluation_prefix l c Y L d M N α hobj hp]
  simpa only [Category.assoc] using
    (first_section_tensor_evaluation_postprefix l c Y L d M N α t hobj)

/-- The section calculation with an arbitrary kernel arrow and an arbitrary functional.
It uses neither a Tate pullback comparison nor a trace base-change equation. In particular,
no integration equation for `d` is used. -/
theorem first_section_tensor_evaluation
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules (coefficient l c).X X) (d : Diagram (coefficient l c).X Y L)
    (M : DerivedCategory (Modules (coefficient l c).X (ProjectiveLine Y)))
    (N : DerivedCategory (Modules (coefficient l c).X (diagonalSurface Y)))
    (α : (DerivedCategory.singleFunctor (Modules (coefficient l c).X (diagonalSurface Y)) 0).obj
      (source (coefficient l c).X Y) ⟶ N)
    (t : d.R₁.R.obj N ⟶ unit (coefficient l c).X (ProjectiveLine Y))
    (hp : IsIso (projectionMap (coefficient l c).X (firstProjection Y) M N)) :
    (moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).map
        (firstKernelInsertion (coefficient l c).X Y M N α) ≫
      firstTerminalFunctional (coefficient l c).X Y L d M N t hp =
    (moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).map
      ((ρ_ M).inv ≫ (M ◁
        ((singleUnitIso (coefficient l c).X (ProjectiveLine Y)).inv ≫ d.support₁.hom ≫
          d.R₁.R.map α ≫ t ≫ (singleUnitIso (coefficient l c).X (ProjectiveLine Y)).hom)) ≫
        (ρ_ M).hom) := by
  delta firstTerminalFunctional
  section_evaluation_exact finish_tensor_evaluation
    (moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)) M
    ((moduleObjectDerivedPushforward (coefficient l c).X (firstProjection Y)).obj N)
    (unit (coefficient l c).X (ProjectiveLine Y))
    ((moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).map
      (firstKernelInsertion (coefficient l c).X Y M N α))
    ((firstPathComparison (coefficient l c).X Y).hom.app
      ((moduleObjectDerivedPullback (coefficient l c).X (firstProjection Y)).obj M ⊗ N))
    (@inv _ _ _ _ (projectionMap (coefficient l c).X (firstProjection Y) M N) hp)
    (firstNativeFunctional (coefficient l c).X Y L d N t)
    (singleUnitIso (coefficient l c).X (ProjectiveLine Y)).inv
    d.support₁.hom (d.R₁.R.map α) t
    (singleUnitIso (coefficient l c).X (ProjectiveLine Y))
    (first_section_tensor_evaluation_core l c Y L d M N α t hp)

end AlgebraicGeometry.ProEtale.RationalP1
