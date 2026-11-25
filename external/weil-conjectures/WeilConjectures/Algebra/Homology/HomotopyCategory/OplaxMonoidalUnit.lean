/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.HomotopyCategory.OplaxMonoidal

/-!
# Left unitality of the comonoidal comparison on complexes

Let `G : C ⥤ D` be an additive oplax monoidal functor which preserves the coproducts defining
the tensor product of homological complexes. Its counit `η : G(𝟙) ⟶ 𝟙` induces a morphism of
complexes `G(𝟙) ⟶ 𝟙` (`CategoryTheory.Functor.OplaxMonoidal.mapHomologicalComplexη`), the unit
complex being `𝟙` placed in degree `0`. Together with the comparison
`G(K ⊗ L) ⟶ G(K) ⊗ G(L)` it satisfies the left unitality axiom of oplax monoidal functors, both
for homological complexes and in the homotopy category.
-/

@[expose] public section

open CategoryTheory Category Limits MonoidalCategory HomologicalComplex

namespace CategoryTheory.Functor.OplaxMonoidal

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  [MonoidalCategory C] [MonoidalCategory D] [HasZeroObject C] [HasZeroObject D]
  [(curriedTensor C).Additive] [∀ (X₁ : C), ((curriedTensor C).obj X₁).Additive]
  [(curriedTensor D).Additive] [∀ (X₁ : D), ((curriedTensor D).obj X₁).Additive]
  {I : Type*} [AddMonoid I] (c : ComplexShape I) [c.TensorSigns] [DecidableEq I]
  [∀ (X₁ X₂ : GradedObject I C), X₁.HasTensor X₂]
  [∀ (X₁ X₂ : GradedObject I D), X₁.HasTensor X₂]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ X₁, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject I C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject I C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject I C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject I D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject I D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject I D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  (G : C ⥤ D) [G.Additive] [G.OplaxMonoidal]
  [∀ j, PreservesColimitsOfShape (Discrete (ComplexShape.π c c c ⁻¹' {j})) G]

/-- The comparison `G(𝟙) ⟶ 𝟙` of complexes induced by the counit `η` of `G`. -/
noncomputable def mapHomologicalComplexη :
    (G.mapHomologicalComplex c).obj (𝟙_ (HomologicalComplex C c)) ⟶
      𝟙_ (HomologicalComplex D c) :=
  (singleMapHomologicalComplex G c 0).hom.app (𝟙_ C) ≫ (single D c 0).map (η G)

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject I C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject I D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ j, PreservesColimitsOfShape (Discrete (ComplexShape.π c c c ⁻¹' {j})) G] in
lemma mapHomologicalComplexη_f_zero :
    (mapHomologicalComplexη c G).f 0 =
      G.map (singleObjXSelf c 0 (𝟙_ C)).hom ≫ η G ≫ (singleObjXSelf c 0 (𝟙_ D)).inv := by
  simp only [mapHomologicalComplexη, comp_f, singleMapHomologicalComplex_hom_app_self,
    single_map_f_self]
  erw [Category.assoc, Iso.inv_hom_id_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Left unitality of the comparison `G(K ⊗ L) ⟶ G(K) ⊗ G(L)` of homological complexes:
`G(λ_K⁻¹) ≫ δ ≫ (η ▷ G K) = λ_{G K}⁻¹`. -/
lemma mapHomologicalComplexδNatTrans_leftUnitor (K : HomologicalComplex C c) :
    (G.mapHomologicalComplex c).map (λ_ K).inv ≫
        ((mapHomologicalComplexδNatTrans c G).app (𝟙_ _)).app K ≫
          mapHomologicalComplexη c G ▷ (G.mapHomologicalComplex c).obj K =
      (λ_ ((G.mapHomologicalComplex c).obj K)).inv := by
  ext i
  have h₁ : (λ_ K).inv.f i = (leftUnitor' K).inv i := rfl
  have h₂ : (λ_ ((G.mapHomologicalComplex c).obj K)).inv.f i =
    (leftUnitor' ((G.mapHomologicalComplex c).obj K)).inv i := rfl
  rw [comp_f, comp_f, Functor.mapHomologicalComplex_map_f, h₁, h₂, leftUnitor'_inv,
    leftUnitor'_inv]
  have h₃ : mapHomologicalComplexη c G ▷ (G.mapHomologicalComplex c).obj K =
    mapBifunctorMap (mapHomologicalComplexη c G) (𝟙 _) _ _ := rfl
  rw [mapHomologicalComplexδNatTrans_app_app, mapBifunctorComparison_f, h₃, G.map_comp,
    G.map_comp]
  simp only [assoc]
  erw [map_ιMapBifunctor_mapBifunctorComparisonX_assoc, ι_mapBifunctorMap]
  simp only [id_f, curriedTensor_map_app, curriedTensor_obj_map,
    mapBifunctorComparisonApp, δNatTrans_app_app, mapHomologicalComplexη_f_zero,
    MonoidalCategory.whiskerLeft_id]
  rw [← δ_natural_left_assoc]
  change _ ≫ _ ≫ (_ ▷ G.obj (K.X i)) ≫ (_ ▷ G.obj (K.X i)) ≫ _ =
    (λ_ (G.obj (K.X i))).inv ≫ (_ ▷ G.obj (K.X i)) ≫ _
  rw [← comp_whiskerRight_assoc, ← G.map_comp_assoc, Iso.inv_hom_id, G.map_id, id_comp,
    comp_whiskerRight_assoc, left_unitality, assoc, assoc]
  erw [id_comp]
  rfl


/-- The comparison `G(𝟙) ⟶ 𝟙` in the homotopy category induced by the counit `η` of `G`. -/
noncomputable def mapHomotopyCategoryη :
    (G.mapHomotopyCategory c).obj (𝟙_ (HomotopyCategory C c)) ⟶ 𝟙_ (HomotopyCategory D c) :=
  (HomotopyCategory.quotient D c).map (mapHomologicalComplexη c G)

set_option backward.isDefEq.respectTransparency false in
/-- Left unitality of the comparison `G(K ⊗ L) ⟶ G(K) ⊗ G(L)` in the homotopy category:
`G(λ_K⁻¹) ≫ δ ≫ (η ▷ G K) = λ_{G K}⁻¹`. -/
lemma mapHomotopyCategoryδNatTrans_leftUnitor (K : HomotopyCategory C c) :
    (G.mapHomotopyCategory c).map (λ_ K).inv ≫
        ((mapHomotopyCategoryδNatTrans c G).app (𝟙_ _)).app K ≫
          mapHomotopyCategoryη c G ▷ (G.mapHomotopyCategory c).obj K =
      (λ_ ((G.mapHomotopyCategory c).obj K)).inv := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  have h₁ : ∀ K : HomologicalComplex C c, (λ_ ((HomotopyCategory.quotient C c).obj K)).inv =
      (HomotopyCategory.quotient C c).map (λ_ K).inv := by
    intro K
    have h : (λ_ ((HomotopyCategory.quotient C c).obj K)).hom =
        (HomotopyCategory.quotient C c).map (λ_ K).hom :=
      HomotopyCategory.MonoidalCategory.leftUnitor_hom_app K
    apply Iso.inv_ext
    rw [h, ← Functor.map_comp, Iso.hom_inv_id, Functor.map_id]
    rfl
  have h₁' : ∀ K : HomologicalComplex D c, (λ_ ((HomotopyCategory.quotient D c).obj K)).inv =
      (HomotopyCategory.quotient D c).map (λ_ K).inv := by
    intro K
    have h : (λ_ ((HomotopyCategory.quotient D c).obj K)).hom =
        (HomotopyCategory.quotient D c).map (λ_ K).hom :=
      HomotopyCategory.MonoidalCategory.leftUnitor_hom_app K
    apply Iso.inv_ext
    rw [h, ← Functor.map_comp, Iso.hom_inv_id, Functor.map_id]
    rfl
  have h₂ : mapHomotopyCategoryη c G ▷ (G.mapHomotopyCategory c).obj
      ((HomotopyCategory.quotient C c).obj K) = (HomotopyCategory.quotient D c).map
        (mapHomologicalComplexη c G ▷ (G.mapHomologicalComplex c).obj K) :=
    (HomotopyCategory.MonoidalCategory.quotient_map_whiskerRight _ _ _ _).symm
  rw [h₁, h₂]
  erw [h₁' ((G.mapHomologicalComplex c).obj K)]
  erw [Functor.mapHomotopyCategory_map, mapHomotopyCategoryδNatTrans_app_app]
  rw [← Functor.map_comp, ← Functor.map_comp, mapHomologicalComplexδNatTrans_leftUnitor]

end CategoryTheory.Functor.OplaxMonoidal
