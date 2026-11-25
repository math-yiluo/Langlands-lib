/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionUnit
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.AdjunctionShift

/-!
# The levelwise derived adjunction commutes with the shifts

Let `adj : f ⊣ g` be an adjunction of exact functors between abelian categories. The levelwise
derived adjunction `D(f) ⊣ D(g)` (`CategoryTheory.Adjunction.mapDerivedCategoryAdjunction`)
commutes with the shifts, for the shift structures of `D(f)` and `D(g)` induced by the
functors on cochain complexes (`CategoryTheory.Adjunction.commShift_mapDerivedCategoryAdjunction`).
Its unit is induced by the unit of the adjunction on homotopy categories, which commutes with
the shifts since the unit on cochain complexes does.
-/

@[expose] public section

open CategoryTheory Category Limits MonoidalCategory Abelian

namespace CategoryTheory.Adjunction

section Homotopy

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive] (adj : L ⊣ R)

/-- The unit of the adjunction induced on cochain complexes commutes with the shifts. -/
instance commShift_mapHomologicalComplex_unit :
    NatTrans.CommShift (adj.mapHomologicalComplex (.up ℤ)).unit ℤ where
  shift_comm n := by
    ext K i
    dsimp [mapHomologicalComplex]
    simp only [Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_id_hom_app,
      HomologicalComplex.id_f, CochainComplex.shiftFunctor_obj_X', Category.id_comp]
    erw [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      Functor.mapHomologicalComplex_commShiftIso_hom_app_f,
      Functor.mapHomologicalComplex_commShiftIso_hom_app_f]
    erw [CategoryTheory.Functor.map_id, Category.comp_id, Category.comp_id]

/-- The unit of the adjunction induced on homotopy categories commutes with the shifts. -/
instance commShift_mapHomotopyCategory_unit :
    NatTrans.CommShift (adj.mapHomotopyCategory (.up ℤ)).unit ℤ := by
  have : Functor.whiskerLeft (HomotopyCategory.quotient C (.up ℤ))
      (adj.mapHomotopyCategory (.up ℤ)).unit =
      (Functor.rightUnitor _).hom ≫ (Functor.leftUnitor _).inv ≫
        Functor.whiskerRight (adj.mapHomologicalComplex (.up ℤ)).unit
          (HomotopyCategory.quotient C (.up ℤ)) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (L.mapHomologicalComplex (.up ℤ))
          (R.mapHomotopyCategoryFactors (.up ℤ)).inv ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (L.mapHomotopyCategoryFactors (.up ℤ)).inv _ ≫
        (Functor.associator _ _ _).hom := by
    ext K
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      mapHomotopyCategory_unit_app_quotient]
    simp [Functor.mapHomotopyCategoryFactors]
  have : NatTrans.CommShift (Functor.whiskerLeft (HomotopyCategory.quotient C (.up ℤ))
      (adj.mapHomotopyCategory (.up ℤ)).unit) ℤ := by
    rw [this]; infer_instance
  exact NatTrans.CommShift.of_whiskerLeft _ (HomotopyCategory.quotient C (.up ℤ))
    (fun X ↦ ⟨_, 𝟙 _, (HomotopyCategory.quotient_obj_surjective X).choose_spec ▸ inferInstance⟩)

end Homotopy

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [MonoidalCategory C] [MonoidalPreadditive C]
  [HasCountableCoproducts C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C]
  [HasDerivedCategory C] [HasDerivedCategory D]
  [HasKInjectiveResolutions D]
  {f : C ⥤ D} {g : D ⥤ C} (adj : f ⊣ g) [f.Additive] [g.Additive]
  [PreservesFiniteLimits f] [PreservesFiniteColimits f]
  [PreservesFiniteLimits g] [PreservesFiniteColimits g]

/-- The levelwise derived adjunction `D(f) ⊣ D(g)` of an adjunction of exact functors commutes
with the shifts. -/
instance commShift_mapDerivedCategoryAdjunction :
    adj.mapDerivedCategoryAdjunction.CommShift ℤ := by
  refine .mk' _ _ ?_
  have e : Functor.whiskerLeft DerivedCategory.Qh adj.mapDerivedCategoryAdjunction.unit =
      (Functor.rightUnitor _).hom ≫ (Functor.leftUnitor _).inv ≫
        Functor.whiskerRight (adj.mapHomotopyCategory (.up ℤ)).unit DerivedCategory.Qh ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (f.mapHomotopyCategory (.up ℤ)) g.mapDerivedCategoryFactorsh.inv ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight f.mapDerivedCategoryFactorsh.inv g.mapDerivedCategory ≫
        (Functor.associator _ _ _).hom := by
    ext X
    have h := adj.mapDerivedCategoryAdjunction_unit_app_Qh_obj X
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Functor.rightUnitor_hom_app,
      Functor.leftUnitor_inv_app, Functor.comp_obj, Functor.id_obj, Category.id_comp,
      Category.comp_id]
    rw [← h]
    simp [← Functor.map_comp]
  have : NatTrans.CommShift
      (Functor.whiskerLeft DerivedCategory.Qh adj.mapDerivedCategoryAdjunction.unit) ℤ := by
    rw [e]; infer_instance
  exact NatTrans.CommShift.of_whiskerLeft _ DerivedCategory.Qh
    (fun X ↦ ⟨_, (DerivedCategory.Qh.objObjPreimageIso X).inv, inferInstance⟩)

end CategoryTheory.Adjunction
