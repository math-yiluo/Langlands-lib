/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryAdjunctionShift
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.AdjunctionShift
public import WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction

/-!
# The unit of a right derived functor commutes with the canonical shifts

The total right derived functor `F.rightDerivedFunctor` carries the shift structure transported
from the K-injective equivalence
(`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated`). This file
shows that its unit `F.mapHomotopyCategory ⋙ Qh ⟶ Qh ⋙ F.rightDerivedFunctor` commutes with
the shifts for this structure (`Functor.commShift_rightDerivedFunctorUnit`), and deduces that
the derived adjunction `L.mapDerivedCategory ⊣ R.rightDerivedFunctor` of an adjunction `L ⊣ R`
with `L` exact commutes with the shifts
(`Adjunction.commShift_mapDerivedCategoryRightDerivedAdjunction`).
-/

@[expose] public section

open CategoryTheory Category Limits Abelian

namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
open CategoryTheory.Functor in
/-- The unit of the total right derived functor commutes with the shifts, for the shift
structure on the right derived functor transported from the K-injective equivalence. -/
instance Functor.commShift_rightDerivedFunctorUnit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] : NatTrans.CommShift F.rightDerivedFunctorUnit ℤ := by
  let inj := ObjectProperty.ι (HomotopyCategory.subcategoryAcyclic C).rightOrthogonal
  let E := HomotopyCategory.KInjectives.equivalence C
  let G := inj ⋙ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  have hI : NatTrans.CommShift F.rightDerivedFunctorIsoKInjectives.inv ℤ :=
    Functor.CommShift.ofIso_compatibility F.rightDerivedFunctorIsoKInjectives.symm ℤ
  have hinv (Y : DerivedCategory C) :
      F.rightDerivedFunctorIsoKInjectives.inv.app Y =
        F.rightDerivedFunctorUnit.app (inj.obj (E.inverse.obj Y)) ≫
          F.rightDerivedFunctor.map (E.counit.app Y) := by
    simp [Functor.rightDerivedFunctorIsoKInjectives, inj, E]
  have hE : E.CommShift ℤ := by infer_instance
  have hU : NatTrans.CommShift E.unitIso.hom ℤ := by infer_instance
  have heq : whiskerLeft inj F.rightDerivedFunctorUnit =
      (leftUnitor G).inv ≫ whiskerRight E.unitIso.hom G ≫
        (associator E.functor E.inverse G).hom ≫
        whiskerLeft E.functor F.rightDerivedFunctorIsoKInjectives.inv ≫
        (associator inj DerivedCategory.Qh F.rightDerivedFunctor).hom := by
    ext X
    simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
      associator_hom_app, leftUnitor_inv_app, Category.id_comp, hinv]
    simp only [Category.assoc]
    erw [Category.id_comp, Category.comp_id]
    have h := F.rightDerivedFunctorUnit.naturality (inj.map (E.unit.app X))
    dsimp only [Functor.comp_map, Functor.comp_obj] at h
    change _ = (F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh).map
      (inj.map (E.unit.app X)) ≫ _
    erw [reassoc_of% h]
    rw [← CategoryTheory.Functor.map_comp]
    change _ = _ ≫ F.rightDerivedFunctor.map
      (E.functor.map (E.unit.app X) ≫ E.counit.app (E.functor.obj X))
    erw [E.functor_unit_comp]
    rw [CategoryTheory.Functor.map_id, Category.comp_id]
  have : NatTrans.CommShift (whiskerLeft inj F.rightDerivedFunctorUnit) ℤ := by
    rw [heq]
    infer_instance
  refine NatTrans.CommShift.of_whiskerLeft _ inj (fun K ↦ ?_)
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  obtain ⟨I, hI, i, hi, _⟩ := HasKInjectiveResolutions.exists_isKInjective P
  have := hI
  have := hi
  refine ⟨HomotopyCategory.KInjectives.mk I,
    (HomotopyCategory.quotient C (.up ℤ)).map i, ?_⟩
  have : IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient C (.up ℤ)).map i)) :=
    (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso C) i).2 inferInstance
  dsimp only [Functor.comp_map]
  infer_instance

namespace Adjunction

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasKInjectiveResolutions D]
  {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L] (adj : L ⊣ R)

/-- The derived adjunction `L.mapDerivedCategory ⊣ R.rightDerivedFunctor` commutes with the
shifts, for the shift structure of `R.rightDerivedFunctor` transported from the K-injective
equivalence: its unit is computed on the homotopy category by the unit of `L ⊣ R` and the unit
of the right derived functor, which commute with the shifts. -/
instance commShift_mapDerivedCategoryRightDerivedAdjunction :
    adj.mapDerivedCategoryRightDerivedAdjunction.CommShift ℤ := by
  refine .mk' _ _ ?_
  have e : Functor.whiskerLeft DerivedCategory.Qh
      adj.mapDerivedCategoryRightDerivedAdjunction.unit =
      (Functor.rightUnitor _).hom ≫ (Functor.leftUnitor _).inv ≫
        Functor.whiskerRight (adj.mapHomotopyCategory (.up ℤ)).unit DerivedCategory.Qh ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (L.mapHomotopyCategory (.up ℤ)) R.rightDerivedFunctorUnit ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight L.mapDerivedCategoryFactorsh.inv R.rightDerivedFunctor ≫
        (Functor.associator _ _ _).hom := by
    ext X
    have h := (adj.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) L.mapDerivedCategoryFactorsh.hom
      R.rightDerivedFunctorUnit X
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Functor.rightUnitor_hom_app,
      Functor.leftUnitor_inv_app, Functor.comp_obj, Functor.id_obj, Category.id_comp,
      Category.comp_id]
    rw [← Category.assoc, ← h, Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
    erw [Functor.map_id, Category.comp_id]
    rfl
  have : NatTrans.CommShift (Functor.whiskerLeft DerivedCategory.Qh
      adj.mapDerivedCategoryRightDerivedAdjunction.unit) ℤ := by
    rw [e]; infer_instance
  exact NatTrans.CommShift.of_whiskerLeft _ DerivedCategory.Qh
    (fun X ↦ ⟨_, (DerivedCategory.Qh.objObjPreimageIso X).inv, inferInstance⟩)

end Adjunction

end CategoryTheory
