/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.IhomUnitTensor

/-!
# Projection maps on cochain complexes

Let `adj : L ⊣ G` be an adjunction with `G` monoidal and both functors additive. On the summand
`G(K^p) ⊗ T^q` of `(G K ⊗ T)^n`, the projection map of the induced adjunction on cochain complexes
is the projection map of `adj`
(`CategoryTheory.Functor.Monoidal.ι_projectionMap_mapHomologicalComplex_f`).
-/

@[expose] public section

open CategoryTheory Category Limits MonoidalCategory HomologicalComplex

namespace CategoryTheory.Functor.Monoidal

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
  {L : D ⥤ C} [L.Additive] (adj : L ⊣ G)

/-- On the summand `G(K^p) ⊗ T^q`, the projection map of `L ⊣ G` on cochain complexes is the
projection map of `L ⊣ G`. -/
lemma ι_projectionMap_mapHomologicalComplex_f (K : CochainComplex C ℤ) (T : CochainComplex D ℤ)
    (p q n : ℤ) (h : p + q = n) :
    L.map (ιTensorObj ((G.mapHomologicalComplex (.up ℤ)).obj K) T p q n h) ≫
        ((projectionMap (adj.mapHomologicalComplex (.up ℤ)) K).app T).f n =
      (projectionMap adj (K.X p)).app (T.X q) ≫
        ιTensorObj K ((L.mapHomologicalComplex (.up ℤ)).obj T) p q n h := by
  have key : ιTensorObj ((G.mapHomologicalComplex (.up ℤ)).obj K) T p q n h ≫
      ((G.mapHomologicalComplex (.up ℤ)).obj K ◁
        (adj.mapHomologicalComplex (.up ℤ)).unit.app T).f n ≫
      (LaxMonoidal.μ (G.mapHomologicalComplex (.up ℤ)) K
        ((L.mapHomologicalComplex (.up ℤ)).obj T)).f n =
      (G.obj (K.X p) ◁ adj.unit.app (T.X q) ≫ LaxMonoidal.μ G (K.X p) (L.obj (T.X q))) ≫
        G.map (ιTensorObj K ((L.mapHomologicalComplex (.up ℤ)).obj T) p q n h) := by
    rw [CochainComplex.ιTensorObj_whiskerLeft_f_assoc, Category.assoc]
    erw [ιTensorObj_mapCochainComplexμIso_hom_f]
    rfl
  simp only [projectionMap, HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    Adjunction.mapHomologicalComplex_counit_app_f]
  rw [L.map_comp, ← Category.assoc, ← Category.assoc, ← L.map_comp, ← L.map_comp,
    Category.assoc, key, L.map_comp, Category.assoc, Category.assoc]
  erw [adj.counit.naturality]
  rfl

/-- If the projection maps of `L ⊣ G` are isomorphisms and `L` preserves the coproducts defining
the tensor product of cochain complexes, then the projection maps of the induced adjunction on
cochain complexes are isomorphisms: degreewise, they are direct sums of projection maps of
`L ⊣ G`. -/
lemma isIso_projectionMap_mapHomologicalComplex (K : CochainComplex C ℤ)
    [∀ X, IsIso (projectionMap adj X)]
    [∀ j, PreservesColimitsOfShape
      (Discrete (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {j})) L] :
    IsIso (projectionMap (adj.mapHomologicalComplex (.up ℤ)) K) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro T
  suffices ∀ n,
      IsIso (((projectionMap (adj.mapHomologicalComplex (.up ℤ)) K).app T).f n) from
    HomologicalComplex.Hom.isIso_of_components _
  intro n
  refine ⟨mapBifunctorDesc fun p q h ↦
    CategoryTheory.inv ((projectionMap adj (K.X p)).app (T.X q)) ≫
    L.map (ιTensorObj ((G.mapHomologicalComplex (.up ℤ)).obj K) T p q n h), ?_, ?_⟩
  · refine HomologicalComplex.mapBifunctor.hom_ext_of_map (c := .up ℤ) L fun p q h ↦ ?_
    rw [reassoc_of% (ι_projectionMap_mapHomologicalComplex_f G adj K T p q n h)]
    erw [ι_mapBifunctorDesc, comp_id]
    rw [IsIso.hom_inv_id_assoc]
  · refine HomologicalComplex.mapBifunctor.hom_ext fun p q h ↦ ?_
    erw [ι_mapBifunctorDesc_assoc]
    rw [Category.assoc, ι_projectionMap_mapHomologicalComplex_f, IsIso.inv_hom_id_assoc]
    exact (comp_id _).symm

end CategoryTheory.Functor.Monoidal
