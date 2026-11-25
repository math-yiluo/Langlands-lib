/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex

/-! # Braided lift of an additive functor to signed cochain complexes

Source: Stacks Project, Tags 06YU and 0FPT.
(blueprint: lem-pur-braided-cochain-normalization).
-/

@[expose] public noncomputable section

attribute [-instance] CategoryTheory.Functor.mapCochainComplexMonoidal

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace CategoryTheory.Functor.OplaxMonoidal

open CategoryTheory.Category HomologicalComplex

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  [MonoidalCategory C] [MonoidalCategory D] [HasZeroObject C] [HasZeroObject D]
  [MonoidalPreadditive C] [MonoidalPreadditive D] [BraidedCategory C] [BraidedCategory D]
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
  (G : C ⥤ D) [G.Additive]
  [∀ j, PreservesColimitsOfShape
    (Discrete (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {j})) G]

private theorem cochain_braiding_delta [G.OplaxMonoidal]
    (hG : ∀ X Y : C, G.map (β_ X Y).hom ≫ δ G Y X = δ G X Y ≫ (β_ (G.obj X) (G.obj Y)).hom)
    (K L : CochainComplex C ℤ) :
    (G.mapHomologicalComplex (.up ℤ)).map (β_ K L).hom ≫
        ((mapHomologicalComplexδNatTrans (.up ℤ) G).app L).app K =
      ((mapHomologicalComplexδNatTrans (.up ℤ) G).app K).app L ≫
        (β_ ((G.mapHomologicalComplex (.up ℤ)).obj K)
          ((G.mapHomologicalComplex (.up ℤ)).obj L)).hom := by
  ext n
  refine mapBifunctor.hom_ext_of_map G (fun p q h ↦ ?_)
  simp only [mapHomologicalComplexδNatTrans_app_app, comp_f, mapBifunctorComparison_f,
    Functor.mapHomologicalComplex_map_f]
  have h₁ := CochainComplex.Monoidal.ι_braiding_hom (K := K) (L := L) p q n h
  have h₂ := CochainComplex.Monoidal.ι_braiding_hom (K := (G.mapHomologicalComplex (.up ℤ)).obj K)
    (L := (G.mapHomologicalComplex (.up ℤ)).obj L) p q n h
  erw [← G.map_comp_assoc, h₁, map_ιMapBifunctor_mapBifunctorComparisonX_assoc, h₂]
  rw [G.map_zsmul, Preadditive.zsmul_comp, Preadditive.comp_zsmul, G.map_comp, assoc]
  erw [map_ιMapBifunctor_mapBifunctorComparisonX]
  simp only [mapBifunctorComparisonApp, δNatTrans_app_app]
  rw [reassoc_of% hG]
  rfl

@[instance_reducible]
private noncomputable def cochainBraided [bg : G.Braided] :
    (G.mapHomologicalComplex (.up ℤ)).Braided := by
  let := Functor.mapCochainComplexMonoidal G
  refine { toMonoidal := inferInstance, braided := ?_ }
  intro P Q
  apply (cancel_mono (Functor.OplaxMonoidal.δ
    (G.mapHomologicalComplex (.up ℤ)) Q P)).1
  have h := Functor.OplaxMonoidal.cochain_braiding_delta G
    (fun X Y ↦ by
      apply (cancel_epi (Functor.LaxMonoidal.μ G X Y)).1
      rw [← Category.assoc, Functor.LaxBraided.braided, Category.assoc,
        Functor.Monoidal.μ_δ, Category.comp_id, Functor.Monoidal.μ_δ_assoc]) P Q
  simp only [← Functor.mapCochainComplex_δ] at h
  rw [Category.assoc, h, Functor.Monoidal.μ_δ_assoc, Category.assoc,
    Functor.Monoidal.μ_δ, Category.comp_id]

private theorem cochainBraided_delta [G.Braided] (P Q : CochainComplex C ℤ) :
    (cochainBraided G).toMonoidal.toOplaxMonoidal.δ P Q = (G.mapCochainComplexμIso P Q).inv := rfl

private theorem cochainBraided_unit [G.Braided] :
    (cochainBraided G).toMonoidal.toOplaxMonoidal.η =
      ((singleMapHomologicalComplex G (.up ℤ) (0 : ℤ)).app (𝟙_ C)).hom ≫
        (single D (.up ℤ) (0 : ℤ)).map (Functor.OplaxMonoidal.η G) := rfl

private theorem cochain_delta_of_summands [G.Braided]
    (P Q : CochainComplex C ℤ)
    (f : (G.mapHomologicalComplex (.up ℤ)).obj (P ⊗ Q) ⟶
      (G.mapHomologicalComplex (.up ℤ)).obj P ⊗ (G.mapHomologicalComplex (.up ℤ)).obj Q)
    (hf : ∀ (p q n : ℤ) (hpq : p + q = n),
      G.map (HomologicalComplex.ιTensorObj P Q p q n hpq) ≫ f.f n =
        δ G (P.X p) (Q.X q) ≫ HomologicalComplex.ιTensorObj
          ((G.mapHomologicalComplex (.up ℤ)).obj P)
          ((G.mapHomologicalComplex (.up ℤ)).obj Q) p q n hpq) :
    f = (G.mapCochainComplexμIso P Q).inv := by
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext_of_map G
  intro p q hpq
  simpa only [Functor.mapCochainComplexμIso_inv,
    mapHomologicalComplexδNatTrans_app_app, HomologicalComplex.mapBifunctorComparison_f,
    HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX,
    HomologicalComplex.mapBifunctorComparisonApp, δNatTrans_app_app] using hf p q n hpq

/-- The cochain lift of an additive braided functor preserves the signed braiding,
with inverse tensorator characterized on total summands and the canonical single unit.

Source: Stacks Project, Tags 06YU and 0FPT; the canonical strong cochain construction of
WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex.
(blueprint: lem-pur-braided-cochain-normalization).

Proof: Use mapCochainComplexMonoidal for the strong structure. On every total summand,
the two braiding composites have the same Koszul sign. The ordinary braided equation
identifies the remaining factors; coproduct extensionality and cancellation prove the
cochain braided equation. The formula for the inverse tensorator on summands and the
coproduct universal property identify any morphism satisfying those formulas. The inverse
unit of the concrete construction is the single-complex comparison followed by the single
of the ordinary inverse unit. This also covers zero objects and zero coefficients. -/
theorem braided_cochain_normalization [G.Braided] :
    ∃ c : (G.mapHomologicalComplex (.up ℤ)).Braided,
      (∀ (P Q : CochainComplex C ℤ)
        (f : (G.mapHomologicalComplex (.up ℤ)).obj (P ⊗ Q) ⟶
          (G.mapHomologicalComplex (.up ℤ)).obj P ⊗ (G.mapHomologicalComplex (.up ℤ)).obj Q),
        (∀ (p q n : ℤ) (hpq : p + q = n),
          G.map (ιTensorObj P Q p q n hpq) ≫ f.f n =
            δ G (P.X p) (Q.X q) ≫ ιTensorObj
              ((G.mapHomologicalComplex (.up ℤ)).obj P)
              ((G.mapHomologicalComplex (.up ℤ)).obj Q) p q n hpq) →
        c.toMonoidal.toOplaxMonoidal.δ P Q = f) ∧
      c.toMonoidal.toOplaxMonoidal.η =
        ((singleMapHomologicalComplex G (.up ℤ) (0 : ℤ)).app (𝟙_ C)).hom ≫
          (single D (.up ℤ) (0 : ℤ)).map (Functor.OplaxMonoidal.η G) := by
  refine ⟨cochainBraided G, ?_, cochainBraided_unit G⟩
  intro P Q f hf
  rw [cochainBraided_delta]
  exact (cochain_delta_of_summands G P Q f hf).symm

end CategoryTheory.Functor.OplaxMonoidal
