/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.HomotopyCategory.MapMonoidal

/-!
# Monoidal isomorphisms of functors on cochain complexes and homotopy categories

Let `G₁ : C ⥤ D`, `G₂ : D ⥤ E` and `G₁₂ : C ⥤ E` be additive monoidal functors preserving the
coproducts defining the tensor products of cochain complexes, and let `e : G₁₂ ≅ G₁ ⋙ G₂` be
compatible with the comparison maps `δ`. Then the induced isomorphism
`G₁₂.mapHomologicalComplex ≅ G₁.mapHomologicalComplex ⋙ G₂.mapHomologicalComplex` is compatible
with the comparison maps `δ` of the induced monoidal functors on cochain complexes
(`CategoryTheory.Functor.mapCochainComplex_δ_comp_tensorHom`), and similarly on homotopy
categories (`CategoryTheory.Functor.mapHomotopyCategory_δ_comp_tensorHom`).
-/

@[expose] public section

open CategoryTheory Category Limits MonoidalCategory HomologicalComplex

namespace CategoryTheory.Functor

open OplaxMonoidal

variable {C D E : Type*} [Category* C] [Category* D] [Category* E] [Preadditive C] [Preadditive D]
  [Preadditive E] [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
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
  (G₁ : C ⥤ D) (G₂ : D ⥤ E) (G₁₂ : C ⥤ E) [G₁.Additive] [G₁.Monoidal] [G₂.Additive]
  [G₂.Monoidal] [G₁₂.Additive] [G₁₂.Monoidal]
  [∀ j, PreservesColimitsOfShape (Discrete (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {j})) G₁]
  [∀ j, PreservesColimitsOfShape (Discrete (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {j})) G₂]
  [∀ j, PreservesColimitsOfShape (Discrete (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {j})) G₁₂]
  (e : G₁₂ ≅ G₁ ⋙ G₂)

/-- The isomorphism `G₁₂(K) ⟶ G₂(G₁(K))` of cochain complexes induced by `e : G₁₂ ≅ G₁ ⋙ G₂`. -/
noncomputable abbrev mapHomologicalComplexCompHom (K : CochainComplex C ℤ) :
    (G₁₂.mapHomologicalComplex (.up ℤ)).obj K ⟶
      (G₂.mapHomologicalComplex (.up ℤ)).obj ((G₁.mapHomologicalComplex (.up ℤ)).obj K) :=
  (NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app K ≫
    (mapHomologicalComplexCompIso (Iso.refl (G₁ ⋙ G₂)) (.up ℤ)).inv.app K

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄] in
/-- On the summand `K.X p ⊗ L.X q`, the tensor product of morphisms of cochain complexes is the
tensor product of their components. -/
@[reassoc]
lemma _root_.CochainComplex.ιTensorObj_tensorHom_f {K K' L L' : CochainComplex C ℤ} (f : K ⟶ K')
    (g : L ⟶ L') (p q n : ℤ) (h : p + q = n) :
    ιTensorObj K L p q n h ≫ (f ⊗ₘ g).f n = (f.f p ⊗ₘ g.f q) ≫ ιTensorObj K' L' p q n h := by
  erw [HomologicalComplex.ι_mapBifunctorMap]
  rw [tensorHom_def, assoc]
  rfl

variable {G₁ G₂ G₁₂ e}

include e in
/-- If `e : G₁₂ ≅ G₁ ⋙ G₂` is compatible with the comparison maps `δ`, then so is the induced
isomorphism of functors on cochain complexes. -/
lemma mapCochainComplex_δ_comp_tensorHom
    (he : ∀ X Y : C, δ G₁₂ X Y ≫ (e.hom.app X ⊗ₘ e.hom.app Y) =
      e.hom.app (X ⊗ Y) ≫ G₂.map (δ G₁ X Y) ≫ δ G₂ _ _)
    (K L : CochainComplex C ℤ) :
    δ (G₁₂.mapHomologicalComplex (.up ℤ)) K L ≫
        (mapHomologicalComplexCompHom G₁ G₂ G₁₂ e K ⊗ₘ
          mapHomologicalComplexCompHom G₁ G₂ G₁₂ e L) =
      mapHomologicalComplexCompHom G₁ G₂ G₁₂ e (K ⊗ L) ≫
        (G₂.mapHomologicalComplex (.up ℤ)).map (δ (G₁.mapHomologicalComplex (.up ℤ)) K L) ≫
        δ (G₂.mapHomologicalComplex (.up ℤ)) _ _ := by
  -- the `μ` form of `he`
  have he' (X Y : C) : (e.hom.app X ⊗ₘ e.hom.app Y) ≫ LaxMonoidal.μ G₂ _ _ ≫
      G₂.map (LaxMonoidal.μ G₁ X Y) = LaxMonoidal.μ G₁₂ X Y ≫ e.hom.app (X ⊗ Y) := by
    rw [← cancel_epi (δ G₁₂ X Y), reassoc_of% (he X Y), Monoidal.δ_μ_assoc,
      ← G₂.map_comp, Monoidal.δ_μ, G₂.map_id]
    simp only [comp_id, Monoidal.δ_μ_assoc]
  rw [mapCochainComplex_δ, mapCochainComplex_δ, mapCochainComplex_δ,
    ← mapCochainComplexμIso_inv, ← mapCochainComplexμIso_inv, ← mapCochainComplexμIso_inv,
    Iso.inv_comp_eq, ← Functor.mapIso_inv]
  simp only [← assoc]
  rw [Iso.eq_comp_inv, Iso.eq_comp_inv, Functor.mapIso_hom]
  simp only [assoc]
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
  erw [CochainComplex.ιTensorObj_tensorHom_f_assoc, ιTensorObj_mapCochainComplexμIso_hom_f_assoc,
    ιTensorObj_mapCochainComplexμIso_hom_f_assoc]
  rw [← G₂.map_comp, ιTensorObj_mapCochainComplexμIso_hom_f, G₂.map_comp]
  simp only [mapHomologicalComplexCompHom, HomologicalComplex.comp_f,
    NatTrans.mapHomologicalComplex_app_f, mapHomologicalComplexCompIso_inv_app_f, Iso.refl_inv,
    NatTrans.id_app]
  erw [comp_id, comp_id]
  erw [reassoc_of% (he' (K.X p) (L.X q))]
  erw [comp_id]
  exact congrArg _ (e.hom.naturality _).symm

variable (G₁ G₂ G₁₂ e) in
/-- The isomorphism `G₁₂(X) ⟶ G₂(G₁(X))` in the homotopy category induced by
`e : G₁₂ ≅ G₁ ⋙ G₂`. -/
noncomputable abbrev mapHomotopyCategoryCompHom (X : HomotopyCategory C (.up ℤ)) :
    (G₁₂.mapHomotopyCategory (.up ℤ)).obj X ⟶
      (G₂.mapHomotopyCategory (.up ℤ)).obj ((G₁.mapHomotopyCategory (.up ℤ)).obj X) :=
  (NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app X ≫
    (mapHomotopyCategoryCompIso (Iso.refl (G₁ ⋙ G₂)) (.up ℤ)).inv.app X

instance (X : HomotopyCategory C (.up ℤ)) : IsIso (mapHomotopyCategoryCompHom G₁ G₂ G₁₂ e X) := by
  have : IsIso ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app X) :=
    ⟨(NatTrans.mapHomotopyCategory e.inv (.up ℤ)).app X, by
      rw [← NatTrans.comp_app, ← NatTrans.mapHomotopyCategory_comp, e.hom_inv_id,
        NatTrans.mapHomotopyCategory_id, NatTrans.id_app], by
      rw [← NatTrans.comp_app, ← NatTrans.mapHomotopyCategory_comp, e.inv_hom_id,
        NatTrans.mapHomotopyCategory_id, NatTrans.id_app]⟩
  dsimp only [mapHomotopyCategoryCompHom]
  infer_instance

include e in
/-- If `e : G₁₂ ≅ G₁ ⋙ G₂` is compatible with the comparison maps `δ`, then so is the induced
isomorphism of functors on homotopy categories. -/
lemma mapHomotopyCategory_δ_comp_tensorHom
    (he : ∀ X Y : C, δ G₁₂ X Y ≫ (e.hom.app X ⊗ₘ e.hom.app Y) =
      e.hom.app (X ⊗ Y) ≫ G₂.map (δ G₁ X Y) ≫ δ G₂ _ _)
    (X Y : HomotopyCategory C (.up ℤ)) :
    δ (G₁₂.mapHomotopyCategory (.up ℤ)) X Y ≫
        (mapHomotopyCategoryCompHom G₁ G₂ G₁₂ e X ⊗ₘ mapHomotopyCategoryCompHom G₁ G₂ G₁₂ e Y) =
      mapHomotopyCategoryCompHom G₁ G₂ G₁₂ e (X ⊗ Y) ≫
        (G₂.mapHomotopyCategory (.up ℤ)).map (δ (G₁.mapHomotopyCategory (.up ℤ)) X Y) ≫
        δ (G₂.mapHomotopyCategory (.up ℤ)) _ _ := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective Y
  have hq (K : CochainComplex C ℤ) :
      mapHomotopyCategoryCompHom G₁ G₂ G₁₂ e ((HomotopyCategory.quotient C (.up ℤ)).obj K) =
        (HomotopyCategory.quotient E (.up ℤ)).map (mapHomologicalComplexCompHom G₁ G₂ G₁₂ e K) := by
    rw [Functor.map_comp]
    congr 1
  rw [hq, hq]
  erw [hq]
  have h := (HomotopyCategory.quotient E (.up ℤ)).congr_map
    (mapCochainComplex_δ_comp_tensorHom he K L)
  simp only [Functor.map_comp, mapCochainComplex_δ,
    ← OplaxMonoidal.mapHomotopyCategoryδNatTrans_app_app, ← mapHomotopyCategory_δ,
    tensorHom_def, HomotopyCategory.MonoidalCategory.quotient_map_whiskerRight',
    HomotopyCategory.MonoidalCategory.quotient_map_whiskerLeft',
    ← Functor.mapHomotopyCategory_map] at h
  simp only [Functor.map_comp, tensorHom_def] at h ⊢
  exact h

end CategoryTheory.Functor
