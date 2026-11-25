/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal

/-!
# A monoidal functor induces a monoidal functor on cochain complexes

Let `G : C ⥤ D` be an additive monoidal functor which preserves the coproducts defining the
tensor product of cochain complexes. Then `G.mapHomologicalComplex (.up ℤ)` is a monoidal
functor (`CategoryTheory.Functor.mapCochainComplexMonoidal`): its comonoidal structure is the
comparison `G(K ⊗ L) ⟶ G(K) ⊗ G(L)`
(`CategoryTheory.Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans`), and its unit is induced
by the unit of `G`.
-/

@[expose] public section

open CategoryTheory Category Limits MonoidalCategory HomologicalComplex

namespace CategoryTheory.Functor

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

/-- The isomorphism `G(K) ⊗ G(L) ≅ G(K ⊗ L)` of cochain complexes, inverse to the comparison
`OplaxMonoidal.mapHomologicalComplexδNatTrans`. -/
noncomputable def mapCochainComplexμIso (K L : CochainComplex C ℤ) :
    (G.mapHomologicalComplex (.up ℤ)).obj K ⊗ (G.mapHomologicalComplex (.up ℤ)).obj L ≅
      (G.mapHomologicalComplex (.up ℤ)).obj (K ⊗ L) :=
  (((asIso (OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) G)).app K).app L).symm

lemma mapCochainComplexμIso_inv (K L : CochainComplex C ℤ) :
    (G.mapCochainComplexμIso K L).inv =
      ((OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) G).app K).app L :=
  rfl

/-- On the summand `G(K.X p) ⊗ G(L.X q)`, the isomorphism `G(K) ⊗ G(L) ≅ G(K ⊗ L)` is the
tensorator of `G`. -/
@[reassoc]
lemma ιTensorObj_mapCochainComplexμIso_hom_f (K L : CochainComplex C ℤ) (p q n : ℤ)
    (h : p + q = n) :
    ιTensorObj ((G.mapHomologicalComplex (.up ℤ)).obj K)
        ((G.mapHomologicalComplex (.up ℤ)).obj L) p q n h ≫
      (G.mapCochainComplexμIso K L).hom.f n =
    LaxMonoidal.μ G (K.X p) (L.X q) ≫ G.map (ιTensorObj K L p q n h) := by
  have h₁ : mapBifunctorComparisonX (OplaxMonoidal.δNatTrans G) (.up ℤ) K L n ≫
      (G.mapCochainComplexμIso K L).hom.f n = 𝟙 _ := by
    rw [← mapBifunctorComparison_f, ← OplaxMonoidal.mapHomologicalComplexδNatTrans_app_app,
      ← mapCochainComplexμIso_inv, ← HomologicalComplex.comp_f, Iso.inv_hom_id,
      HomologicalComplex.id_f]
    rfl
  have h₂ := map_ιMapBifunctor_mapBifunctorComparisonX (OplaxMonoidal.δNatTrans G) (.up ℤ)
    K L p q n h
  calc _ = (LaxMonoidal.μ G (K.X p) (L.X q) ≫ OplaxMonoidal.δ G (K.X p) (L.X q)) ≫
        ιTensorObj ((G.mapHomologicalComplex (.up ℤ)).obj K)
          ((G.mapHomologicalComplex (.up ℤ)).obj L) p q n h ≫
        (G.mapCochainComplexμIso K L).hom.f n := by rw [Monoidal.μ_δ, id_comp]
    _ = LaxMonoidal.μ G (K.X p) (L.X q) ≫ G.map (ιTensorObj K L p q n h) ≫
        mapBifunctorComparisonX (OplaxMonoidal.δNatTrans G) (.up ℤ) K L n ≫
        (G.mapCochainComplexμIso K L).hom.f n := by
      erw [reassoc_of% h₂]; rw [assoc]; rfl
    _ = _ := by rw [h₁, comp_id]

/-- The unit `𝟙_ ≅ G(𝟙_)` of cochain complexes, induced by the unit of `G`. -/
noncomputable def mapCochainComplexεIso :
    𝟙_ (CochainComplex D ℤ) ≅ (G.mapHomologicalComplex (.up ℤ)).obj (𝟙_ (CochainComplex C ℤ)) :=
  (single D (.up ℤ) 0).mapIso (Monoidal.εIso G) ≪≫
    ((singleMapHomologicalComplex G (.up ℤ) 0).app (𝟙_ C)).symm

omit [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ j, PreservesColimitsOfShape
    (Discrete (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {j})) G] in
lemma mapCochainComplexεIso_hom_f_zero :
    (G.mapCochainComplexεIso).hom.f 0 =
      (singleObjXSelf (.up ℤ) 0 (𝟙_ D)).hom ≫ LaxMonoidal.ε G ≫
        G.map (singleObjXSelf (.up ℤ) 0 (𝟙_ C)).inv := by
  simp [mapCochainComplexεIso, single_map_f_self]

@[reassoc]
lemma mapCochainComplexμIso_hom_naturality_left {K K' : CochainComplex C ℤ} (f : K ⟶ K')
    (L : CochainComplex C ℤ) :
    (G.mapHomologicalComplex (.up ℤ)).map f ▷ (G.mapHomologicalComplex (.up ℤ)).obj L ≫
      (G.mapCochainComplexμIso K' L).hom =
    (G.mapCochainComplexμIso K L).hom ≫ (G.mapHomologicalComplex (.up ℤ)).map (f ▷ L) := by
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  simp only [HomologicalComplex.comp_f]
  erw [CochainComplex.Monoidal.ι_whiskerRight_assoc, ιTensorObj_mapCochainComplexμIso_hom_f,
    ιTensorObj_mapCochainComplexμIso_hom_f_assoc]
  simp only [Functor.mapHomologicalComplex_map_f]
  erw [LaxMonoidal.μ_natural_left_assoc]
  rw [← G.map_comp, ← G.map_comp, CochainComplex.Monoidal.ι_whiskerRight]

@[reassoc]
lemma mapCochainComplexμIso_hom_naturality_right (K : CochainComplex C ℤ)
    {L L' : CochainComplex C ℤ} (f : L ⟶ L') :
    (G.mapHomologicalComplex (.up ℤ)).obj K ◁ (G.mapHomologicalComplex (.up ℤ)).map f ≫
      (G.mapCochainComplexμIso K L').hom =
    (G.mapCochainComplexμIso K L).hom ≫ (G.mapHomologicalComplex (.up ℤ)).map (K ◁ f) := by
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  simp only [HomologicalComplex.comp_f]
  erw [CochainComplex.ιTensorObj_whiskerLeft_f_assoc, ιTensorObj_mapCochainComplexμIso_hom_f,
    ιTensorObj_mapCochainComplexμIso_hom_f_assoc]
  simp only [Functor.mapHomologicalComplex_map_f]
  erw [LaxMonoidal.μ_natural_right_assoc]
  rw [← G.map_comp, ← G.map_comp, CochainComplex.ιTensorObj_whiskerLeft_f]

@[reassoc]
lemma whiskerLeft_ιTensorObj_mapCochainComplexμIso_hom_f (X : D) (K L : CochainComplex C ℤ)
    (p q n : ℤ) (h : p + q = n) :
    X ◁ ιTensorObj ((G.mapHomologicalComplex (.up ℤ)).obj K)
        ((G.mapHomologicalComplex (.up ℤ)).obj L) p q n h ≫
      X ◁ (G.mapCochainComplexμIso K L).hom.f n =
    X ◁ LaxMonoidal.μ G (K.X p) (L.X q) ≫ X ◁ G.map (ιTensorObj K L p q n h) := by
  rw [← MonoidalCategory.whiskerLeft_comp, ← MonoidalCategory.whiskerLeft_comp]
  erw [ιTensorObj_mapCochainComplexμIso_hom_f]

@[reassoc]
lemma ιTensorObj_mapCochainComplexμIso_hom_f_whiskerRight (X : D) (K L : CochainComplex C ℤ)
    (p q n : ℤ) (h : p + q = n) :
    ιTensorObj ((G.mapHomologicalComplex (.up ℤ)).obj K)
        ((G.mapHomologicalComplex (.up ℤ)).obj L) p q n h ▷ X ≫
      (G.mapCochainComplexμIso K L).hom.f n ▷ X =
    LaxMonoidal.μ G (K.X p) (L.X q) ▷ X ≫ G.map (ιTensorObj K L p q n h) ▷ X := by
  have := congrArg (· ▷ X) (G.ιTensorObj_mapCochainComplexμIso_hom_f K L p q n h)
  simp only [comp_whiskerRight] at this
  exact this

lemma mapCochainComplexμIso_associativity (K L M : CochainComplex C ℤ) :
    (G.mapCochainComplexμIso K L).hom ▷ (G.mapHomologicalComplex (.up ℤ)).obj M ≫
      (G.mapCochainComplexμIso (K ⊗ L) M).hom ≫
        (G.mapHomologicalComplex (.up ℤ)).map (α_ K L M).hom =
    (α_ ((G.mapHomologicalComplex (.up ℤ)).obj K) ((G.mapHomologicalComplex (.up ℤ)).obj L)
        ((G.mapHomologicalComplex (.up ℤ)).obj M)).hom ≫
      (G.mapHomologicalComplex (.up ℤ)).obj K ◁ (G.mapCochainComplexμIso L M).hom ≫
        (G.mapCochainComplexμIso K (L ⊗ M)).hom := by
  ext n : 1
  apply HomologicalComplex.mapBifunctor₁₂.hom_ext
  intro p q r h
  have h' : p + q + r = n := h
  have h'' : p + (q + r) = n := by rw [← h', add_assoc]
  have key : (ιTensorObj K L p q (p + q) rfl ▷ M.X r) ≫ ιTensorObj (K ⊗ L) M (p + q) r n h' ≫
      (α_ K L M).hom.f n =
      (α_ (K.X p) (L.X q) (M.X r)).hom ≫ (K.X p ◁ ιTensorObj L M q r (q + r) rfl) ≫
        ιTensorObj K (L ⊗ M) p (q + r) n h'' := by
    rw [← CochainComplex.Monoidal.ι₂₃_eq _ _ _ p q r (q + r) n rfl h'',
      ← CochainComplex.Monoidal.ι₁₂_associator_hom _ _ _ p q r n h',
      CochainComplex.Monoidal.ι₁₂_eq _ _ _ p q r (p + q) n rfl h', assoc]
  have key' := congrArg G.map key
  simp only [Functor.map_comp] at key'
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
  erw [CochainComplex.Monoidal.ι₁₂_eq _ _ _ p q r (p + q) n rfl h',
    CochainComplex.Monoidal.ι₁₂_associator_hom_assoc,
    CochainComplex.Monoidal.ι₂₃_eq _ _ _ p q r (q + r) n rfl h'']
  on_goal 2 => exact h'
  simp only [assoc]
  erw [CochainComplex.Monoidal.ι_whiskerRight_assoc, CochainComplex.ιTensorObj_whiskerLeft_f_assoc,
    ιTensorObj_mapCochainComplexμIso_hom_f_whiskerRight_assoc,
    whiskerLeft_ιTensorObj_mapCochainComplexμIso_hom_f_assoc,
    ιTensorObj_mapCochainComplexμIso_hom_f_assoc, ιTensorObj_mapCochainComplexμIso_hom_f]
  erw [LaxMonoidal.μ_natural_left_assoc, LaxMonoidal.μ_natural_right_assoc, key']
  exact LaxMonoidal.associativity_assoc G _ _ _ _

lemma mapCochainComplex_leftUnitor_inv (K : CochainComplex C ℤ) :
    (λ_ ((G.mapHomologicalComplex (.up ℤ)).obj K)).inv ≫
      G.mapCochainComplexεIso.hom ▷ (G.mapHomologicalComplex (.up ℤ)).obj K ≫
        (G.mapCochainComplexμIso (𝟙_ _) K).hom =
    (G.mapHomologicalComplex (.up ℤ)).map (λ_ K).inv := by
  ext i
  have e : ∀ (X : CochainComplex D ℤ), (λ_ X).inv.f i = (leftUnitor' X).inv i := fun _ ↦ rfl
  have e' : ∀ (X : CochainComplex C ℤ), (λ_ X).inv.f i = (leftUnitor' X).inv i := fun _ ↦ rfl
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f, e, e']
  erw [leftUnitor'_inv, leftUnitor'_inv]
  simp only [assoc]
  erw [CochainComplex.Monoidal.ι_whiskerRight_assoc, ιTensorObj_mapCochainComplexμIso_hom_f]
  rw [mapCochainComplexεIso_hom_f_zero]
  simp only [comp_whiskerRight, assoc, Functor.map_comp, inv_hom_whiskerRight_assoc]
  erw [LaxMonoidal.μ_natural_left_assoc, LaxMonoidal.left_unitality_inv_assoc]
  rfl

lemma mapCochainComplex_rightUnitor_inv (K : CochainComplex C ℤ) :
    (ρ_ ((G.mapHomologicalComplex (.up ℤ)).obj K)).inv ≫
      (G.mapHomologicalComplex (.up ℤ)).obj K ◁ G.mapCochainComplexεIso.hom ≫
        (G.mapCochainComplexμIso K (𝟙_ _)).hom =
    (G.mapHomologicalComplex (.up ℤ)).map (ρ_ K).inv := by
  ext i
  have e : ∀ (X : CochainComplex D ℤ), (ρ_ X).inv.f i = (rightUnitor' X).inv i := fun _ ↦ rfl
  have e' : ∀ (X : CochainComplex C ℤ), (ρ_ X).inv.f i = (rightUnitor' X).inv i := fun _ ↦ rfl
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f, e, e']
  erw [rightUnitor'_inv, rightUnitor'_inv]
  simp only [assoc]
  erw [CochainComplex.ιTensorObj_whiskerLeft_f_assoc, ιTensorObj_mapCochainComplexμIso_hom_f]
  rw [mapCochainComplexεIso_hom_f_zero]
  erw [MonoidalCategory.whiskerLeft_comp, MonoidalCategory.whiskerLeft_comp]
  simp only [assoc, Functor.map_comp, MonoidalCategory.whiskerLeft_inv_hom_assoc]
  erw [LaxMonoidal.μ_natural_right_assoc, LaxMonoidal.right_unitality_inv_assoc]
  rfl

/-- An additive monoidal functor `G` which preserves the coproducts defining the tensor product
of cochain complexes induces a monoidal functor `G.mapHomologicalComplex (.up ℤ)` on cochain
complexes. -/
noncomputable instance mapCochainComplexMonoidal : (G.mapHomologicalComplex (.up ℤ)).Monoidal :=
  CoreMonoidal.toMonoidal
    { εIso := G.mapCochainComplexεIso
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
          Functor.map_id] }

lemma mapCochainComplex_δ (K L : CochainComplex C ℤ) :
    OplaxMonoidal.δ (G.mapHomologicalComplex (.up ℤ)) K L =
      ((OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) G).app K).app L :=
  rfl

lemma mapCochainComplex_η :
    OplaxMonoidal.η (G.mapHomologicalComplex (.up ℤ)) = G.mapCochainComplexεIso.inv :=
  rfl

end CategoryTheory.Functor
