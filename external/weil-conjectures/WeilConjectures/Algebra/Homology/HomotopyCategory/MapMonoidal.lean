/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.HomotopyCategory.OplaxMonoidal
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex

/-!
# A monoidal functor induces an oplax monoidal functor on homotopy categories

Let `G : C ⥤ D` be an additive monoidal functor which preserves the coproducts defining the
tensor product of cochain complexes. The monoidal structure of
`G.mapHomologicalComplex (.up ℤ)` (`CategoryTheory.Functor.mapCochainComplexMonoidal`) descends
to an oplax monoidal structure on `G.mapHomotopyCategory (.up ℤ)`
(`CategoryTheory.Functor.mapHomotopyCategoryOplaxMonoidal`), whose comonoidal structure is
`CategoryTheory.Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans`.
-/

@[expose] public section

open CategoryTheory Category Limits MonoidalCategory HomologicalComplex

namespace HomotopyCategory.MonoidalCategory

variable {C : Type*} [Category* C] [Preadditive C] [MonoidalCategory C] [HasZeroObject C]
  [MonoidalPreadditive C]
  [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

lemma quotient_associator_hom (K L M : CochainComplex C ℤ) :
    (α_ ((quotient C (.up ℤ)).obj K) ((quotient C (.up ℤ)).obj L)
      ((quotient C (.up ℤ)).obj M)).hom = (quotient C (.up ℤ)).map (α_ K L M).hom :=
  associator_hom_app_app_app K L M

lemma quotient_leftUnitor_inv (K : CochainComplex C ℤ) :
    (λ_ ((quotient C (.up ℤ)).obj K)).inv = (quotient C (.up ℤ)).map (λ_ K).inv := by
  have h : (λ_ ((quotient C (.up ℤ)).obj K)).hom = (quotient C (.up ℤ)).map (λ_ K).hom :=
    leftUnitor_hom_app K
  rw [← cancel_mono (λ_ _).hom, Iso.inv_hom_id, h]
  rw [← CategoryTheory.Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]

lemma quotient_rightUnitor_inv (K : CochainComplex C ℤ) :
    (ρ_ ((quotient C (.up ℤ)).obj K)).inv = (quotient C (.up ℤ)).map (ρ_ K).inv := by
  have h : (ρ_ ((quotient C (.up ℤ)).obj K)).hom = (quotient C (.up ℤ)).map (ρ_ K).hom :=
    rightUnitor_hom_app K
  rw [← cancel_mono (ρ_ _).hom, Iso.inv_hom_id, h]
  rw [← CategoryTheory.Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]

lemma quotient_map_whiskerRight' {K₁ L₁ : CochainComplex C ℤ} (f₁ : K₁ ⟶ L₁)
    (K₂ : CochainComplex C ℤ) :
    (quotient C (.up ℤ)).map (f₁ ▷ K₂) =
      (quotient C (.up ℤ)).map f₁ ▷ (quotient C (.up ℤ)).obj K₂ :=
  quotient_map_whiskerRight C (.up ℤ) f₁ K₂

lemma quotient_map_whiskerLeft' (K₁ : CochainComplex C ℤ) {K₂ L₂ : CochainComplex C ℤ}
    (f₂ : K₂ ⟶ L₂) :
    (quotient C (.up ℤ)).map (K₁ ◁ f₂) =
      (quotient C (.up ℤ)).obj K₁ ◁ (quotient C (.up ℤ)).map f₂ :=
  quotient_map_whiskerLeft C (.up ℤ) K₁ f₂

end HomotopyCategory.MonoidalCategory

namespace CategoryTheory.Functor

open HomotopyCategory.MonoidalCategory


variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  [MonoidalCategory C] [MonoidalCategory D] [HasZeroObject C] [HasZeroObject D]
  [MonoidalPreadditive C] [MonoidalPreadditive D]
  [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ (X₁ X₂ : GradedObject ℤ D), X₁.HasTensor X₂]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ X₁, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  (G : C ⥤ D) [G.Additive] [G.Monoidal]
  [∀ j, PreservesColimitsOfShape
    (Discrete (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {j})) G]

/-- The oplax monoidal structure on `G.mapHomotopyCategory (.up ℤ)` induced by the monoidal
structure of `G.mapHomologicalComplex (.up ℤ)`. Its comonoidal structure is
`OplaxMonoidal.mapHomotopyCategoryδNatTrans`. -/
noncomputable instance mapHomotopyCategoryOplaxMonoidal :
    (G.mapHomotopyCategory (.up ℤ)).OplaxMonoidal where
  η := (HomotopyCategory.quotient D (.up ℤ)).map
    (OplaxMonoidal.η (G.mapHomologicalComplex (.up ℤ)))
  δ X Y := ((OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) G).app X).app Y
  δ_natural_left f X' :=
    (congr_app ((OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) G).naturality f) X').symm
  δ_natural_right X f :=
    (((OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) G).app X).naturality f).symm
  oplax_associativity X Y Z := by
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective Y
    obtain ⟨M, rfl⟩ := HomotopyCategory.quotient_obj_surjective Z
    have h := (HomotopyCategory.quotient D (.up ℤ)).congr_map
      (OplaxMonoidal.associativity (G.mapHomologicalComplex (.up ℤ)) K L M)
    simp only [Functor.map_comp, mapCochainComplex_δ,
      ← OplaxMonoidal.mapHomotopyCategoryδNatTrans_app_app, quotient_map_whiskerRight',
      quotient_map_whiskerLeft', ← Functor.mapHomotopyCategory_map, ← quotient_associator_hom] at h
    exact h
  oplax_left_unitality X := by
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    have h := (HomotopyCategory.quotient D (.up ℤ)).congr_map
      (OplaxMonoidal.left_unitality (G.mapHomologicalComplex (.up ℤ)) K)
    simp only [Functor.map_comp, mapCochainComplex_δ,
      ← OplaxMonoidal.mapHomotopyCategoryδNatTrans_app_app, quotient_map_whiskerRight',
      ← Functor.mapHomotopyCategory_map, ← quotient_leftUnitor_inv] at h
    exact h
  oplax_right_unitality X := by
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    have h := (HomotopyCategory.quotient D (.up ℤ)).congr_map
      (OplaxMonoidal.right_unitality (G.mapHomologicalComplex (.up ℤ)) K)
    simp only [Functor.map_comp, mapCochainComplex_δ,
      ← OplaxMonoidal.mapHomotopyCategoryδNatTrans_app_app, quotient_map_whiskerLeft',
      ← Functor.mapHomotopyCategory_map, ← quotient_rightUnitor_inv] at h
    exact h

lemma mapHomotopyCategory_δ (X Y : HomotopyCategory C (.up ℤ)) :
    OplaxMonoidal.δ (G.mapHomotopyCategory (.up ℤ)) X Y =
      ((OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) G).app X).app Y :=
  rfl

lemma mapHomotopyCategory_η :
    OplaxMonoidal.η (G.mapHomotopyCategory (.up ℤ)) =
      (HomotopyCategory.quotient D (.up ℤ)).map
        (OplaxMonoidal.η (G.mapHomologicalComplex (.up ℤ))) :=
  rfl

end CategoryTheory.Functor
