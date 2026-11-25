/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
public import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimit
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.StrictRoosComparison

set_option linter.privateModule false

/-!
# The strict Roos comparison and its evaluation maps

Source: Stacks Project, Derived Categories, Tags 07KC and 08TC, and Cohomology on Sites,
Tags 0940 and 0941; the explicit comparison and evaluation square in the blueprint proof
(auxiliary; not a blueprint node).

The helper definitions spell out the products, transition endomorphism and signed cone
already introduced by this statement. The comparison maps are uniquely specified by
coordinates, rather than chosen as arbitrary isomorphisms of derived-limit triangles.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w uC vC r

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

variable {A : Type u} [Category.{v} A] [Abelian A] [HasCountableProducts A]

set_option backward.isDefEq.respectTransparency false in
private def strictTowerLimitIso [HasLimitsOfShape ℕᵒᵖ A] :
    HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
      (lim : (ℕᵒᵖ ⥤ CochainComplex A ℤ) ⥤ CochainComplex A ℤ) ≅
        (lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ) :=
  NatIso.ofComponents (fun X ↦
    limit.isoLimitCone ⟨HomologicalComplex.coneOfHasLimitEval X.asFunctor,
      HomologicalComplex.isLimitConeOfHasLimitEval X.asFunctor⟩) (by
    intro X Y f
    apply (HomologicalComplex.isLimitConeOfHasLimitEval Y.asFunctor).hom_ext
    intro n
    ext p
    have hπ (Z : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
        (limit.isoLimitCone ⟨HomologicalComplex.coneOfHasLimitEval Z.asFunctor,
          HomologicalComplex.isLimitConeOfHasLimitEval Z.asFunctor⟩).hom.f p ≫
            limit.π (Z.X p) n = (limit.π Z.asFunctor n).f p := by
      simpa only [HomologicalComplex.comp_f,
        HomologicalComplex.coneOfHasLimitEval_π_app_f, HomologicalComplex.asFunctor,
        HomologicalComplex.eval, Functor.comp] using
        congrArg (fun f ↦ HomologicalComplex.Hom.f f p)
          (limit.isoLimitCone_hom_π
            ⟨HomologicalComplex.coneOfHasLimitEval Z.asFunctor,
              HomologicalComplex.isLimitConeOfHasLimitEval Z.asFunctor⟩ n)
    have hm := congrArg (fun f ↦ HomologicalComplex.Hom.f f p)
      (limMap_π (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f) n)
    dsimp at hπ hm ⊢
    simp only [HomologicalComplex.coneOfHasLimitEval_π_app_f,
      HomologicalComplex.asFunctor, HomologicalComplex.eval, Functor.comp] at hπ hm ⊢
    calc
      _ = (limMap (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f)).f p ≫
          (limit.π Y.asFunctor n).f p := by
        rw [Category.assoc, hπ Y]
        rfl
      _ = (limit.π X.asFunctor n).f p ≫ (f.f p).app n := hm
      _ = _ := by
        rw [Category.assoc]
        change _ = _ ≫ limMap (f.f p) ≫ limit.π (Y.X p) n
        rw [limMap_π, ← Category.assoc, hπ X]
        rfl)

end CategoryTheory
