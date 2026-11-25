/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs

/-!
# Additivity of the right derived functor

The right derived functor `F.rightDerivedFunctor : DerivedCategory C ⥤ DerivedCategory D` of an
additive functor `F` between abelian categories, where `C` has K-injective resolutions, is
additive: it is computed on K-injective representatives, on which it is induced by the additive
functor `F` on homotopy categories, and the localization functors are additive. Since the
K-injective complexes form a full subcategory of the homotopy category equivalent to the derived
category, this shows that `F.rightDerivedFunctor` is additive.
-/

@[expose] public section

open CategoryTheory Abelian

variable {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasKInjectiveResolutions C]

open HomotopyCategory.KInjectives in
/-- **The right derived functor of an additive functor is additive.** -/
instance CategoryTheory.Functor.additive_rightDerivedFunctor (F : C ⥤ D) [F.Additive] :
    F.rightDerivedFunctor.Additive := by
  have : (ι (C := C)).Additive := by unfold ι; infer_instance
  have h (X : HomotopyCategory.KInjectives C) :
      IsIso (F.rightDerivedFunctorUnit.app (ι.obj X)) :=
    (localizerMorphism_derives _).isIso_of_isRightDerivedFunctor F.rightDerivedFunctorUnit X
  have : (Qh (C := C) ⋙ F.rightDerivedFunctor).Additive :=
    Functor.additive_of_iso (NatIso.ofComponents
      (F := ι ⋙ F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
      (fun X ↦ @asIso _ _ _ _ (F.rightDerivedFunctorUnit.app (ι.obj X)) (h X))
      (fun _ ↦ F.rightDerivedFunctorUnit.naturality _))
  have : (Qh (C := C)).Additive := by unfold Qh; infer_instance
  exact Functor.additive_of_full_essSurj_comp Qh _
