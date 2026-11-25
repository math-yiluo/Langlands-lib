/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory
public import WeilConjectures.Mathlib.CategoryTheory.Shift.CommShift

/-!
# The identity isomorphisms of induced functors commute with the shifts

The isomorphisms `(𝟭 C).mapHomologicalComplex ≅ 𝟭`, `(𝟭 C).mapHomotopyCategory ≅ 𝟭` and
`(𝟭 C).mapDerivedCategory ≅ 𝟭` commute with the shifts.
-/

@[expose] public section

open CategoryTheory Category Limits

namespace CategoryTheory.Functor

variable (C : Type*) [Category C]

instance commShift_mapHomologicalComplexIdIso_hom [Preadditive C] :
    NatTrans.CommShift (mapHomologicalComplexIdIso C (ComplexShape.up ℤ)).hom ℤ where
  shift_comm n := by
    ext K i
    simp [mapHomologicalComplexIdIso]

set_option backward.isDefEq.respectTransparency false in
instance commShift_mapHomotopyCategoryIdIso_hom [Preadditive C] [HasZeroObject C] :
    NatTrans.CommShift (mapHomotopyCategoryIdIso C (ComplexShape.up ℤ)).hom ℤ := by
  have e : whiskerLeft (HomotopyCategory.quotient C (ComplexShape.up ℤ))
      (mapHomotopyCategoryIdIso C (ComplexShape.up ℤ)).hom =
      ((𝟭 C).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom ≫
        whiskerRight (mapHomologicalComplexIdIso C (ComplexShape.up ℤ)).hom
          (HomotopyCategory.quotient C (ComplexShape.up ℤ)) ≫
        (HomotopyCategory.quotient C (ComplexShape.up ℤ)).leftUnitor.hom ≫
        (HomotopyCategory.quotient C (ComplexShape.up ℤ)).rightUnitor.inv := by
    ext K
    dsimp
    rw [mapHomotopyCategoryIdIso_hom_app]
    simp only [id_obj, comp_id]
    exact (Category.id_comp _).symm
  have : NatTrans.CommShift (whiskerLeft (HomotopyCategory.quotient C (ComplexShape.up ℤ))
      (mapHomotopyCategoryIdIso C (ComplexShape.up ℤ)).hom) ℤ := by
    rw [e]
    infer_instance
  exact NatTrans.CommShift.of_whiskerLeft _ (HomotopyCategory.quotient C (ComplexShape.up ℤ))
    (fun K ↦ ⟨_, ((HomotopyCategory.quotient C _).objObjPreimageIso K).inv, inferInstance⟩)

set_option backward.isDefEq.respectTransparency false in
instance commShift_mapDerivedCategoryIdIso_hom [Abelian C] [HasDerivedCategory C] :
    NatTrans.CommShift (mapDerivedCategoryIdIso C).hom ℤ := by
  have e : whiskerLeft DerivedCategory.Qh (mapDerivedCategoryIdIso C).hom =
      (𝟭 C).mapDerivedCategoryFactorsh.hom ≫
        whiskerRight (mapHomotopyCategoryIdIso C (ComplexShape.up ℤ)).hom DerivedCategory.Qh ≫
        DerivedCategory.Qh.leftUnitor.hom ≫ DerivedCategory.Qh.rightUnitor.inv := by
    have h := congrArg Iso.hom (mapDerivedCategoryIdIso_factorsh C)
    simp only [Iso.trans_hom, isoWhiskerLeft_hom, isoWhiskerRight_hom] at h
    rw [← reassoc_of% h]
    ext K
    simp
  have : NatTrans.CommShift (whiskerLeft DerivedCategory.Qh (mapDerivedCategoryIdIso C).hom)
      ℤ := by
    rw [e]
    infer_instance
  exact NatTrans.CommShift.of_whiskerLeft _ DerivedCategory.Qh
    (fun X ↦ ⟨_, (DerivedCategory.Qh.objObjPreimageIso X).inv, inferInstance⟩)

end CategoryTheory.Functor
