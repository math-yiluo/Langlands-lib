/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex

/-! # Coherence of termwise monoidal functors on cochain complexes

Source: Stacks Project, Cohomology on Sites, Tag 07A4.

For an additive monoidal functor `G` preserving the coproducts of total tensor products,
`G.mapCochainComplexMonoidal` makes the termwise functor monoidal. This file records the
underlying `CoreMonoidal` structure, its value on the total-tensor summands, the Koszul
braiding compatibility and the compatibility with a compositor.
-/

@[expose] public section

open CategoryTheory Category Limits MonoidalCategory HomologicalComplex

namespace CategoryTheory.Functor

section Single

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

/-- The `CoreMonoidal` structure underlying `mapCochainComplexMonoidal`. -/
noncomputable def mapCochainComplexCoreMonoidal :
    (G.mapHomologicalComplex (.up ℤ)).CoreMonoidal where
  εIso := G.mapCochainComplexεIso
  μIso := G.mapCochainComplexμIso
  μIso_hom_natural_left := G.mapCochainComplexμIso_hom_naturality_left
  μIso_hom_natural_right K f := G.mapCochainComplexμIso_hom_naturality_right K f
  associativity := G.mapCochainComplexμIso_associativity
  left_unitality K := by
    rw [← cancel_epi (λ_ _).inv, Iso.inv_hom_id, reassoc_of% mapCochainComplex_leftUnitor_inv,
      ← Functor.map_comp, Iso.inv_hom_id, Functor.map_id]
  right_unitality K := by
    rw [← cancel_epi (ρ_ _).inv, Iso.inv_hom_id,
      reassoc_of% mapCochainComplex_rightUnitor_inv, ← Functor.map_comp, Iso.inv_hom_id,
      Functor.map_id]

/-- On a total-tensor summand, the inverse comparison is the comonoidal structure of `G`. -/
@[reassoc]
lemma map_ιTensorObj_mapCochainComplexμIso_inv_f (K L : CochainComplex C ℤ) (p q n : ℤ)
    (h : p + q = n) :
    G.map (ιTensorObj K L p q n h) ≫ (G.mapCochainComplexμIso K L).inv.f n =
      OplaxMonoidal.δ G (K.X p) (L.X q) ≫
        ιTensorObj ((G.mapHomologicalComplex (.up ℤ)).obj K)
          ((G.mapHomologicalComplex (.up ℤ)).obj L) p q n h := by
  rw [← cancel_mono ((G.mapCochainComplexμIso K L).hom.f n), assoc, assoc,
    ← HomologicalComplex.comp_f, Iso.inv_hom_id, HomologicalComplex.id_f]
  erw [comp_id, ιTensorObj_mapCochainComplexμIso_hom_f, Monoidal.δ_μ_assoc]

/-- A braided comonoidal structure on `G` gives the Koszul braiding compatibility of the
termwise functor. -/
lemma mapCochainComplex_braiding [BraidedCategory C] [BraidedCategory D]
    (hβ : ∀ X Y : C, G.map (β_ X Y).hom ≫ OplaxMonoidal.δ G Y X =
      OplaxMonoidal.δ G X Y ≫ (β_ (G.obj X) (G.obj Y)).hom)
    (K L : CochainComplex C ℤ) :
    (G.mapHomologicalComplex (.up ℤ)).map (CochainComplex.Monoidal.braiding K L).hom ≫
        (G.mapCochainComplexμIso L K).inv =
      (G.mapCochainComplexμIso K L).inv ≫
        (CochainComplex.Monoidal.braiding ((G.mapHomologicalComplex (.up ℤ)).obj K)
          ((G.mapHomologicalComplex (.up ℤ)).obj L)).hom := by
  rw [Iso.comp_inv_eq, assoc, Iso.eq_inv_comp]
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  have hμ : LaxMonoidal.μ G (K.X p) (L.X q) ≫ G.map (β_ (K.X p) (L.X q)).hom =
      (β_ (G.obj (K.X p)) (G.obj (L.X q))).hom ≫ LaxMonoidal.μ G (L.X q) (K.X p) := by
    rw [← cancel_epi (OplaxMonoidal.δ G (K.X p) (L.X q)), Monoidal.δ_μ_assoc,
      ← reassoc_of% (hβ (K.X p) (L.X q)), Monoidal.δ_μ, comp_id]
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
  erw [ιTensorObj_mapCochainComplexμIso_hom_f_assoc, CochainComplex.Monoidal.ι_braiding_hom_assoc]
  rw [← G.map_comp, CochainComplex.Monoidal.ι_braiding_hom, Functor.map_zsmul,
    Preadditive.comp_zsmul, Preadditive.zsmul_comp, G.map_comp, reassoc_of% hμ, assoc]
  erw [ιTensorObj_mapCochainComplexμIso_hom_f]
  rfl

end Single

section Composition

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Preadditive C] [Preadditive D] [Preadditive E]
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
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
  (G₁ : C ⥤ D) [G₁.Additive] [G₁.Monoidal]
  [∀ j, PreservesColimitsOfShape
    (Discrete (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {j})) G₁]
  (G₂ : D ⥤ E) [G₂.Additive] [G₂.Monoidal]
  [∀ j, PreservesColimitsOfShape
    (Discrete (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {j})) G₂]
  (G₁₂ : C ⥤ E) [G₁₂.Additive] [G₁₂.Monoidal]
  [∀ j, PreservesColimitsOfShape
    (Discrete (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {j})) G₁₂]

/-- A compositor compatible with the comonoidal structures gives the composition law of
the termwise comparisons. Writing `G` for the termwise functor on cochain complexes,
`δ` for the inverse of `mapCochainComplexμIso` and `a` for the termwise compositor:
```
  G₁₂(P ⊗ Q) ──────── δ ───────→ G₁₂ P ⊗ G₁₂ Q
      │ a                              │ a ⊗ a
      ↓                                ↓
  G₂ G₁(P ⊗ Q) ─ G₂ δ → G₂(G₁ P ⊗ G₁ Q) ─ δ → G₂ G₁ P ⊗ G₂ G₁ Q
```
-/
lemma mapCochainComplex_composition (a : G₁₂ ≅ G₁ ⋙ G₂)
    (ha : ∀ M N : C, OplaxMonoidal.δ G₁₂ M N ≫ (a.hom.app M ⊗ₘ a.hom.app N) =
      a.hom.app (M ⊗ N) ≫ G₂.map (OplaxMonoidal.δ G₁ M N) ≫
        OplaxMonoidal.δ G₂ (G₁.obj M) (G₁.obj N))
    (P Q : CochainComplex C ℤ) :
    (G₁₂.mapCochainComplexμIso P Q).inv ≫
        ((Functor.mapHomologicalComplexCompIso a.symm (.up ℤ)).symm.hom.app P ⊗ₘ
          (Functor.mapHomologicalComplexCompIso a.symm (.up ℤ)).symm.hom.app Q) =
      (Functor.mapHomologicalComplexCompIso a.symm (.up ℤ)).symm.hom.app (P ⊗ Q) ≫
        (G₂.mapHomologicalComplex (.up ℤ)).map (G₁.mapCochainComplexμIso P Q).inv ≫
          (G₂.mapCochainComplexμIso ((G₁.mapHomologicalComplex (.up ℤ)).obj P)
            ((G₁.mapHomologicalComplex (.up ℤ)).obj Q)).inv := by
  have hμ (M N : C) : (a.hom.app M ⊗ₘ a.hom.app N) ≫ LaxMonoidal.μ G₂ (G₁.obj M) (G₁.obj N) ≫
      G₂.map (LaxMonoidal.μ G₁ M N) = LaxMonoidal.μ G₁₂ M N ≫ a.hom.app (M ⊗ N) := by
    rw [← cancel_epi (OplaxMonoidal.δ G₁₂ M N), reassoc_of% (ha M N), Monoidal.δ_μ_assoc,
      Monoidal.δ_μ_assoc, ← G₂.map_comp, Monoidal.δ_μ, G₂.map_id, comp_id]
  rw [Iso.inv_comp_eq]
  simp only [← assoc]
  rw [Iso.eq_comp_inv, ← Functor.mapIso_inv, Iso.eq_comp_inv, Functor.mapIso_hom]
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f, tensorHom_def,
    assoc, Iso.symm_hom, Functor.mapHomologicalComplexCompIso_inv_app_f, Iso.symm_inv]
  erw [CochainComplex.Monoidal.ι_whiskerRight_assoc, CochainComplex.ιTensorObj_whiskerLeft_f_assoc,
    ιTensorObj_mapCochainComplexμIso_hom_f_assoc, ιTensorObj_mapCochainComplexμIso_hom_f_assoc]
  rw [← G₂.map_comp, ιTensorObj_mapCochainComplexμIso_hom_f, G₂.map_comp,
    ← tensorHom_def_assoc]
  simp only [Functor.mapHomologicalComplexCompIso_inv_app_f, Iso.symm_inv]
  erw [reassoc_of% (hμ (P.X p) (Q.X q)), a.hom.naturality]
  rfl

end Composition

end CategoryTheory.Functor
