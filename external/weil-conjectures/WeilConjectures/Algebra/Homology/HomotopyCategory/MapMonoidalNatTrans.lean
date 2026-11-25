/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.HomotopyCategory.MapMonoidal

/-!
# Monoidal natural transformations and the units on complexes

Let `F : C ⥤ D`, `G : D ⥤ E` and `H : C ⥤ E` be additive monoidal functors preserving the
coproducts defining the tensor products of cochain complexes, and let `τ : H ⟶ F ⋙ G` be a
natural transformation. Applying `τ` in every degree gives morphisms `H(K) ⟶ G(F(K))` of cochain
complexes, and of objects of the homotopy categories. If `τ` is monoidal, they are compatible with
the units of the induced functors on complexes
(`CategoryTheory.Functor.mapCochainComplexεIso_hom_mapHomologicalComplexCompNatTrans`) and with
the counits of the comonoidal structures of the induced functors on homotopy categories
(`CategoryTheory.Functor.mapHomotopyCategoryCompNatTrans_η`). The compatibility with the tensor
products is `CategoryTheory.Functor.mapHomotopyCategory_δ_comp_tensorHom`.
-/

@[expose] public section

open CategoryTheory Category Limits MonoidalCategory HomologicalComplex

namespace CategoryTheory.Functor

open HomotopyCategory.MonoidalCategory

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Preadditive C] [Preadditive D] [Preadditive E]
  (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E) [F.Additive] [G.Additive] [H.Additive]
  (τ : H ⟶ F ⋙ G)

/-- The morphism `H(K) ⟶ G(F(K))` of cochain complexes given by `τ` in every degree. -/
noncomputable def mapHomologicalComplexCompNatTrans (K : CochainComplex C ℤ) :
    (H.mapHomologicalComplex (.up ℤ)).obj K ⟶
      (G.mapHomologicalComplex (.up ℤ)).obj ((F.mapHomologicalComplex (.up ℤ)).obj K) :=
  (NatTrans.mapHomologicalComplex τ (.up ℤ)).app K ≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv.app K

@[simp]
lemma mapHomologicalComplexCompNatTrans_f (K : CochainComplex C ℤ) (n : ℤ) :
    (mapHomologicalComplexCompNatTrans F G H τ K).f n = τ.app (K.X n) := by
  simp only [mapHomologicalComplexCompNatTrans, HomologicalComplex.comp_f,
    NatTrans.mapHomologicalComplex_app_f, Functor.mapHomologicalComplexCompIso_inv_app_f,
    Iso.refl_inv]
  erw [Category.comp_id]

/-- The morphism `H(P) ⟶ G(F(P))` of the homotopy category given by `τ` in every degree. -/
noncomputable def mapHomotopyCategoryCompNatTrans (P : HomotopyCategory C (.up ℤ)) :
    (H.mapHomotopyCategory (.up ℤ)).obj P ⟶
      (G.mapHomotopyCategory (.up ℤ)).obj ((F.mapHomotopyCategory (.up ℤ)).obj P) :=
  (NatTrans.mapHomotopyCategory τ (.up ℤ)).app P ≫
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv.app P

lemma mapHomotopyCategoryCompNatTrans_quotient (K : CochainComplex C ℤ) :
    mapHomotopyCategoryCompNatTrans F G H τ ((HomotopyCategory.quotient C (.up ℤ)).obj K) =
      (HomotopyCategory.quotient E (.up ℤ)).map (mapHomologicalComplexCompNatTrans F G H τ K) := by
  simp only [mapHomotopyCategoryCompNatTrans, mapHomologicalComplexCompNatTrans,
    Functor.map_comp]
  rfl

variable [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
  [HasZeroObject C] [HasZeroObject D] [HasZeroObject E]
  [MonoidalPreadditive C] [MonoidalPreadditive D] [MonoidalPreadditive E]
  [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ (X₁ X₂ : GradedObject ℤ D), X₁.HasTensor X₂]
  [∀ (X₁ X₂ : GradedObject ℤ E), X₁.HasTensor X₂]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ X₁, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).flip.obj X₂)]
  [∀ X₁, PreservesColimit (Functor.empty.{0} E) ((curriedTensor E).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} E) ((curriedTensor E).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ E), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ E), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ E), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [F.Monoidal] [G.Monoidal] [H.Monoidal]
  [∀ j, PreservesColimitsOfShape
    (Discrete (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {j})) F]
  [∀ j, PreservesColimitsOfShape
    (Discrete (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {j})) G]
  [∀ j, PreservesColimitsOfShape
    (Discrete (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {j})) H]
  [NatTrans.IsMonoidal τ]

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ E), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ j, PreservesColimitsOfShape
    (Discrete (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {j})) F]
  [∀ j, PreservesColimitsOfShape
    (Discrete (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {j})) G]
  [∀ j, PreservesColimitsOfShape
    (Discrete (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {j})) H] in
/-- The morphisms `H(K) ⟶ G(F(K))` are compatible with the units of the monoidal structures of
the induced functors on cochain complexes. -/
lemma mapCochainComplexεIso_hom_mapHomologicalComplexCompNatTrans :
    H.mapCochainComplexεIso.hom ≫ mapHomologicalComplexCompNatTrans F G H τ (𝟙_ _) =
      G.mapCochainComplexεIso.hom ≫
        (G.mapHomologicalComplex (.up ℤ)).map F.mapCochainComplexεIso.hom := by
  apply HomologicalComplex.from_single_hom_ext
  simp only [HomologicalComplex.comp_f, mapHomologicalComplexCompNatTrans_f,
    Functor.mapHomologicalComplex_map_f, mapCochainComplexεIso_hom_f_zero, Category.assoc,
    Functor.map_comp]
  have hnat := τ.naturality (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ C)).inv
  have hmon := NatTrans.IsMonoidal.unit (τ := τ)
  simp only [Functor.comp_obj, Functor.comp_map, Functor.LaxMonoidal.comp_ε] at hnat hmon
  erw [hnat]
  rw [reassoc_of% hmon, ← G.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
    Category.id_comp]

/-- The morphisms `H(P) ⟶ G(F(P))` are compatible with the counits of the oplax monoidal
structures of the induced functors on the homotopy categories. -/
lemma mapHomotopyCategoryCompNatTrans_η :
    mapHomotopyCategoryCompNatTrans F G H τ (𝟙_ _) ≫
        (G.mapHomotopyCategory (.up ℤ)).map (OplaxMonoidal.η (F.mapHomotopyCategory (.up ℤ))) ≫
          OplaxMonoidal.η (G.mapHomotopyCategory (.up ℤ)) =
      OplaxMonoidal.η (H.mapHomotopyCategory (.up ℤ)) := by
  simp only [Functor.mapHomotopyCategory_η, Functor.mapCochainComplex_η]
  erw [mapHomotopyCategoryCompNatTrans_quotient]
  simp only [Functor.mapHomotopyCategory_map, ← Functor.map_comp]
  congr 1
  rw [← cancel_epi H.mapCochainComplexεIso.hom, Iso.hom_inv_id,
    ← Category.assoc, mapCochainComplexεIso_hom_mapHomologicalComplexCompNatTrans,
    Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
    Category.id_comp, Iso.hom_inv_id]

end CategoryTheory.Functor
