/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.System.SystemLevelLeftExtensionBasic
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # The actual derived transitions of strict systems

Source: Zheng, Construction 4.1; Stacks 015F.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w})

/-- Localize the strict transition and use the canonical exact-functor compositor.
Source: Zheng 4.1; Stacks 015F (blueprint: lem-pur-system-derived-transition). -/
def systemDerivedTransition {m n : ℕ} (h : m ≤ n) :
    derivedSystemEvaluation B n ⟶
      derivedSystemEvaluation B m ⋙ (systemRestriction B h).mapDerivedCategory :=
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso (StrictRingSystem B) (.up ℤ)) _ _
    (systemEvaluation B n).mapDerivedCategory
    (systemEvaluation B m ⋙ systemRestriction B h).mapDerivedCategory
    (Functor.whiskerRight
      (NatTrans.mapHomologicalComplex (strictSystemTransition B h) (.up ℤ))
      DerivedCategory.Q) ≫
    (Functor.mapDerivedCategoryCompIso (systemEvaluation B m) (systemRestriction B h)).inv

/-- The localized transition is represented by the original strict transition.
Source: Zheng 4.1; Stacks 015F (blueprint: lem-pur-system-derived-transition).
Proof: the formula for the lifted natural transformation gives its value on Q(K).
The canonical exact-functor compositor cancels against the two evaluation factorizations,
leaving precisely the localized termwise strict transition. -/
theorem systemDerivedTransition_rep {m n : ℕ} (h : m ≤ n)
    (K : CochainComplex (StrictRingSystem B) ℤ) :
    (systemDerivedTransition B h).app (DerivedCategory.Q.obj K) ≫
      (systemRestriction B h).mapDerivedCategory.map
        ((systemEvaluation B m).mapDerivedCategoryFactors.hom.app K) ≫
      (systemRestriction B h).mapDerivedCategoryFactors.hom.app
        (((systemEvaluation B m).mapHomologicalComplex (.up ℤ)).obj K) =
    (systemEvaluation B n).mapDerivedCategoryFactors.hom.app K ≫
      DerivedCategory.Q.map
        ((strictSystemTransition B h).mapHomologicalComplex (.up ℤ) |>.app K) := by
  dsimp only [systemDerivedTransition, NatTrans.comp_app]
  rw [Category.assoc, Functor.mapDerivedCategoryCompIso_hom_app_factors]
  rw [Localization.liftNatTrans_app]
  change ((systemEvaluation B n).mapDerivedCategoryFactors.hom.app K ≫
    DerivedCategory.Q.map
      ((strictSystemTransition B h).mapHomologicalComplex (.up ℤ) |>.app K) ≫
    (systemEvaluation B m ⋙ systemRestriction B h).mapDerivedCategoryFactors.inv.app K) ≫
    (systemEvaluation B m ⋙ systemRestriction B h).mapDerivedCategoryFactors.hom.app K = _
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]

end SheafOfModules
