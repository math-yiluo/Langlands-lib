/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionUnit

/-!
# Mates and the functors induced on derived categories

Let `adj₁ : f₁ ⊣ g₁` and `adj₂ : f₂ ⊣ g₂` be adjunctions of exact functors, and let
`β : u ⋙ f₂ ≅ f₁ ⋙ v` be the mate of `τ : g₁ ⋙ u ≅ v ⋙ g₂` for exact `u` and `v`. Then the
isomorphism induced by `β` on derived categories is the mate of the one induced by `τ`, for the
levelwise derived adjunctions `D(f₁) ⊣ D(g₁)` and `D(f₂) ⊣ D(g₂)`
(`CategoryTheory.Adjunction.mapDerivedCategoryAdjunction_mate`).
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory Abelian

namespace CategoryTheory

namespace Functor

section NatIso

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D] [HasDerivedCategory C]
  [HasDerivedCategory D] {F G H : C ⥤ D} [F.Additive] [PreservesFiniteLimits F]
  [PreservesFiniteColimits F] [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]

lemma mapDerivedCategoryNatIso_refl :
    (mapDerivedCategoryNatIso (Iso.refl F)).hom = 𝟙 _ := by
  refine Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso C (.up ℤ))
    (fun K ↦ ?_)
  rw [← cancel_mono (F.mapDerivedCategoryFactors.hom.app K), mapDerivedCategoryNatIso_fac]
  simp

lemma mapDerivedCategoryNatIso_trans (e₁ : F ≅ G) (e₂ : G ≅ H) :
    (mapDerivedCategoryNatIso (e₁ ≪≫ e₂)).hom =
      (mapDerivedCategoryNatIso e₁).hom ≫ (mapDerivedCategoryNatIso e₂).hom := by
  refine Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso C (.up ℤ))
    (fun K ↦ ?_)
  rw [← cancel_mono (H.mapDerivedCategoryFactors.hom.app K), mapDerivedCategoryNatIso_fac,
    NatTrans.comp_app, Category.assoc, mapDerivedCategoryNatIso_fac,
    mapDerivedCategoryNatIso_fac_assoc, Iso.trans_hom, NatTrans.mapHomologicalComplex_comp,
    NatTrans.comp_app, Functor.map_comp]

lemma mapDerivedCategoryNatIso_symm (e : F ≅ G) :
    (mapDerivedCategoryNatIso e.symm).hom = (mapDerivedCategoryNatIso e).inv := by
  rw [← cancel_epi (mapDerivedCategoryNatIso e).hom, Iso.hom_inv_id,
    ← mapDerivedCategoryNatIso_trans, Iso.self_symm_id, mapDerivedCategoryNatIso_refl]

end NatIso

variable {A B B' E : Type*} [Category A] [Category B] [Category B'] [Category E] [Abelian A]
  [Abelian B] [Abelian B'] [Abelian E] [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory B'] [HasDerivedCategory E]
  {F₁ : A ⥤ B} {F₂ : B ⥤ E} {G₁ : A ⥤ B'} {G₂ : B' ⥤ E}
  [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  [G₁.Additive] [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
  [G₂.Additive] [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]

/-- The isomorphism `D(F₁) ⋙ D(F₂) ≅ D(G₁) ⋙ D(G₂)` induced by `e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂`. -/
noncomputable abbrev mapDerivedCategorySquareIso (e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂) :
    F₁.mapDerivedCategory ⋙ F₂.mapDerivedCategory ≅
      G₁.mapDerivedCategory ⋙ G₂.mapDerivedCategory :=
  mapDerivedCategoryCompIso F₁ F₂ ≪≫ mapDerivedCategoryNatIso e ≪≫
    (mapDerivedCategoryCompIso G₁ G₂).symm

/-- On the image `Qh X` of an object of the homotopy category, the isomorphism
`D(F₁) ⋙ D(F₂) ≅ D(G₁) ⋙ D(G₂)` induced by `e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂` is the image of the
isomorphism induced by `e` on homotopy categories. -/
lemma mapDerivedCategorySquareIso_hom_app_Qh_obj (e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂)
    (X : HomotopyCategory A (.up ℤ)) :
    F₂.mapDerivedCategoryFactorsh.inv.app ((F₁.mapHomotopyCategory (.up ℤ)).obj X) ≫
        F₂.mapDerivedCategory.map (F₁.mapDerivedCategoryFactorsh.inv.app X) ≫
        (mapDerivedCategorySquareIso e).hom.app (DerivedCategory.Qh.obj X) ≫
        G₂.mapDerivedCategory.map (G₁.mapDerivedCategoryFactorsh.hom.app X) ≫
        G₂.mapDerivedCategoryFactorsh.hom.app ((G₁.mapHomotopyCategory (.up ℤ)).obj X) =
      DerivedCategory.Qh.map
        ((mapHomotopyCategoryCompIso (Iso.refl (F₁ ⋙ F₂)) (.up ℤ)).hom.app X ≫
          (NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app X ≫
          (mapHomotopyCategoryCompIso (Iso.refl (G₁ ⋙ G₂)) (.up ℤ)).inv.app X) := by
  have hF := mapDerivedCategoryCompIso_fach F₁ F₂ X
  have hG := mapDerivedCategoryCompIso_fach G₁ G₂ X
  have he := mapDerivedCategoryNatIso_fach e X
  have hG' : (mapDerivedCategoryCompIso G₁ G₂).inv.app (DerivedCategory.Qh.obj X) ≫
      G₂.mapDerivedCategory.map (G₁.mapDerivedCategoryFactorsh.hom.app X) ≫
      G₂.mapDerivedCategoryFactorsh.hom.app ((G₁.mapHomotopyCategory (.up ℤ)).obj X) =
      (G₁ ⋙ G₂).mapDerivedCategoryFactorsh.hom.app X ≫ DerivedCategory.Qh.map
        ((mapHomotopyCategoryCompIso (Iso.refl (G₁ ⋙ G₂)) (.up ℤ)).inv.app X) := by
    rw [← hG]
    simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  have hF' : F₂.mapDerivedCategoryFactorsh.inv.app ((F₁.mapHomotopyCategory (.up ℤ)).obj X) ≫
      F₂.mapDerivedCategory.map (F₁.mapDerivedCategoryFactorsh.inv.app X) ≫
      (mapDerivedCategoryCompIso F₁ F₂).hom.app (DerivedCategory.Qh.obj X) =
      DerivedCategory.Qh.map
        ((mapHomotopyCategoryCompIso (Iso.refl (F₁ ⋙ F₂)) (.up ℤ)).hom.app X) ≫
        (F₁ ⋙ F₂).mapDerivedCategoryFactorsh.inv.app X := by
    rw [← cancel_mono ((F₁ ⋙ F₂).mapDerivedCategoryFactorsh.hom.app X)]
    simp only [Category.assoc, Iso.inv_hom_id_app]
    rw [← hF, Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc]
    exact (Category.comp_id _).symm
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  rw [reassoc_of% hF', hG', reassoc_of% he, Iso.inv_hom_id_app_assoc]
  simp only [Functor.map_comp]


section Triangle

variable {A B E : Type*} [Category A] [Category B] [Category E] [Abelian A] [Abelian B]
  [Abelian E] [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory E]
  {F₁ : A ⥤ B} {G₁ : B ⥤ E} {F₂ : A ⥤ E}
  [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [G₁.Additive] [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
  [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]

/-- The isomorphism `D(F₂) ≅ D(F₁) ⋙ D(G₁)` induced by `e : F₂ ≅ F₁ ⋙ G₁`. -/
noncomputable abbrev mapDerivedCategoryTriangleIso (e : F₂ ≅ F₁ ⋙ G₁) :
    F₂.mapDerivedCategory ≅ F₁.mapDerivedCategory ⋙ G₁.mapDerivedCategory :=
  mapDerivedCategoryNatIso e ≪≫ (mapDerivedCategoryCompIso F₁ G₁).symm

/-- On the image `Qh X` of an object of the homotopy category, the isomorphism
`D(F₂) ≅ D(F₁) ⋙ D(G₁)` induced by `e : F₂ ≅ F₁ ⋙ G₁` is the image of the isomorphism induced
by `e` on homotopy categories. -/
lemma mapDerivedCategoryTriangleIso_hom_app_Qh_obj (e : F₂ ≅ F₁ ⋙ G₁)
    (X : HomotopyCategory A (.up ℤ)) :
    F₂.mapDerivedCategoryFactorsh.inv.app X ≫
        (mapDerivedCategoryTriangleIso e).hom.app (DerivedCategory.Qh.obj X) ≫
        G₁.mapDerivedCategory.map (F₁.mapDerivedCategoryFactorsh.hom.app X) ≫
        G₁.mapDerivedCategoryFactorsh.hom.app ((F₁.mapHomotopyCategory (.up ℤ)).obj X) =
      DerivedCategory.Qh.map
        ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app X ≫
          (mapHomotopyCategoryCompIso (Iso.refl (F₁ ⋙ G₁)) (.up ℤ)).inv.app X) := by
  have hG := mapDerivedCategoryCompIso_fach F₁ G₁ X
  have he := mapDerivedCategoryNatIso_fach e X
  have hG' : (mapDerivedCategoryCompIso F₁ G₁).inv.app (DerivedCategory.Qh.obj X) ≫
      G₁.mapDerivedCategory.map (F₁.mapDerivedCategoryFactorsh.hom.app X) ≫
      G₁.mapDerivedCategoryFactorsh.hom.app ((F₁.mapHomotopyCategory (.up ℤ)).obj X) =
      (F₁ ⋙ G₁).mapDerivedCategoryFactorsh.hom.app X ≫ DerivedCategory.Qh.map
        ((mapHomotopyCategoryCompIso (Iso.refl (F₁ ⋙ G₁)) (.up ℤ)).inv.app X) := by
    rw [← hG]
    simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  rw [hG', reassoc_of% he, Iso.inv_hom_id_app_assoc]
  simp only [Functor.map_comp]

end Triangle
end Functor

namespace Adjunction

variable {C₁ D₁ C₂ D₂ : Type*} [Category C₁] [Category D₁] [Category C₂] [Category D₂]
  [Abelian C₁] [Abelian D₁] [Abelian C₂] [Abelian D₂]
  [MonoidalCategory C₁] [MonoidalPreadditive C₁] [HasCountableCoproducts C₁]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C₁), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C₁), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C₁), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ C₁] [HasExactColimitsOfShape ℤ C₁]
  [∀ (X : C₁), PreservesColimitsOfShape ℤ ((curriedTensor C₁).obj X)]
  [∀ (X : C₁), PreservesColimitsOfShape ℤ ((curriedTensor C₁).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C₁]
  [MonoidalCategory C₂] [MonoidalPreadditive C₂] [HasCountableCoproducts C₂]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C₂), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C₂), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C₂), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ C₂] [HasExactColimitsOfShape ℤ C₂]
  [∀ (X : C₂), PreservesColimitsOfShape ℤ ((curriedTensor C₂).obj X)]
  [∀ (X : C₂), PreservesColimitsOfShape ℤ ((curriedTensor C₂).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C₂]
  [HasDerivedCategory C₁] [HasDerivedCategory D₁] [HasDerivedCategory C₂]
  [HasDerivedCategory D₂] [HasKInjectiveResolutions D₁] [HasKInjectiveResolutions D₂]
  {f₁ : C₁ ⥤ D₁} {g₁ : D₁ ⥤ C₁} (adj₁ : f₁ ⊣ g₁) {f₂ : C₂ ⥤ D₂} {g₂ : D₂ ⥤ C₂}
  (adj₂ : f₂ ⊣ g₂) {u : C₁ ⥤ C₂} {v : D₁ ⥤ D₂}
  [f₁.Additive] [PreservesFiniteLimits f₁] [PreservesFiniteColimits f₁]
  [g₁.Additive] [PreservesFiniteLimits g₁] [PreservesFiniteColimits g₁]
  [f₂.Additive] [PreservesFiniteLimits f₂] [PreservesFiniteColimits f₂]
  [g₂.Additive] [PreservesFiniteLimits g₂] [PreservesFiniteColimits g₂]
  [u.Additive] [PreservesFiniteLimits u] [PreservesFiniteColimits u]
  [v.Additive] [PreservesFiniteLimits v] [PreservesFiniteColimits v]
  (τ : g₁ ⋙ u ≅ v ⋙ g₂) (β : u ⋙ f₂ ≅ f₁ ⋙ v)

include adj₁ adj₂ in
lemma mapDerivedCategoryAdjunction_mate_Qh_obj
    (hβ : ∀ K, adj₂.unit.app (u.obj K) ≫ g₂.map (β.hom.app K) =
      u.map (adj₁.unit.app K) ≫ τ.hom.app (f₁.obj K))
    (X : HomotopyCategory C₁ (.up ℤ)) :
    adj₂.mapDerivedCategoryAdjunction.unit.app
        (u.mapDerivedCategory.obj (DerivedCategory.Qh.obj X)) ≫
        g₂.mapDerivedCategory.map
          ((Functor.mapDerivedCategorySquareIso β).hom.app (DerivedCategory.Qh.obj X)) =
      u.mapDerivedCategory.map
          (adj₁.mapDerivedCategoryAdjunction.unit.app (DerivedCategory.Qh.obj X)) ≫
        (Functor.mapDerivedCategorySquareIso τ).hom.app
          (f₁.mapDerivedCategory.obj (DerivedCategory.Qh.obj X)) := by
  -- reduce to a computation in the homotopy category
  rw [← cancel_epi (u.mapDerivedCategoryFactorsh.inv.app X),
    ← cancel_mono (g₂.mapDerivedCategory.map (v.mapDerivedCategory.map
      (f₁.mapDerivedCategoryFactorsh.hom.app X)) ≫
      g₂.mapDerivedCategory.map (v.mapDerivedCategoryFactorsh.hom.app
        ((f₁.mapHomotopyCategory (.up ℤ)).obj X)) ≫
      g₂.mapDerivedCategoryFactorsh.hom.app
        ((v.mapHomotopyCategory (.up ℤ)).obj ((f₁.mapHomotopyCategory (.up ℤ)).obj X)))]
  -- the left hand side
  have h₁ := adj₂.mapDerivedCategoryAdjunction.unit.naturality
    (u.mapDerivedCategoryFactorsh.inv.app X)
  have h₂ := adj₂.mapDerivedCategoryAdjunction_unit_app_Qh_obj
    ((u.mapHomotopyCategory (.up ℤ)).obj X)
  have h₃ := Functor.mapDerivedCategorySquareIso_hom_app_Qh_obj β X
  have h₄ := g₂.mapDerivedCategoryFactorsh.hom.naturality
    ((Functor.mapHomotopyCategoryCompIso (Iso.refl (u ⋙ f₂)) (.up ℤ)).hom.app X ≫
      (NatTrans.mapHomotopyCategory β.hom (.up ℤ)).app X ≫
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (f₁ ⋙ v)) (.up ℤ)).inv.app X)
  dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at h₁ h₄
  have h₂' : adj₂.mapDerivedCategoryAdjunction.unit.app
      (DerivedCategory.Qh.obj ((u.mapHomotopyCategory (.up ℤ)).obj X)) =
      DerivedCategory.Qh.map ((adj₂.mapHomotopyCategory (.up ℤ)).unit.app
        ((u.mapHomotopyCategory (.up ℤ)).obj X)) ≫
        g₂.mapDerivedCategoryFactorsh.inv.app _ ≫
        g₂.mapDerivedCategory.map (f₂.mapDerivedCategoryFactorsh.inv.app _) := by
    rw [← h₂]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
    rw [← Functor.map_comp, Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  have h₃' := congrArg g₂.mapDerivedCategory.map h₃
  simp only [Functor.map_comp] at h₃'
  have hL : u.mapDerivedCategoryFactorsh.inv.app X ≫
      adj₂.mapDerivedCategoryAdjunction.unit.app
        (u.mapDerivedCategory.obj (DerivedCategory.Qh.obj X)) ≫
      g₂.mapDerivedCategory.map
        ((Functor.mapDerivedCategorySquareIso β).hom.app (DerivedCategory.Qh.obj X)) ≫
      g₂.mapDerivedCategory.map (v.mapDerivedCategory.map
        (f₁.mapDerivedCategoryFactorsh.hom.app X)) ≫
      g₂.mapDerivedCategory.map (v.mapDerivedCategoryFactorsh.hom.app
        ((f₁.mapHomotopyCategory (.up ℤ)).obj X)) ≫
      g₂.mapDerivedCategoryFactorsh.hom.app
        ((v.mapHomotopyCategory (.up ℤ)).obj ((f₁.mapHomotopyCategory (.up ℤ)).obj X)) =
      DerivedCategory.Qh.map ((adj₂.mapHomotopyCategory (.up ℤ)).unit.app
        ((u.mapHomotopyCategory (.up ℤ)).obj X) ≫ (g₂.mapHomotopyCategory (.up ℤ)).map
          ((Functor.mapHomotopyCategoryCompIso (Iso.refl (u ⋙ f₂)) (.up ℤ)).hom.app X ≫
            (NatTrans.mapHomotopyCategory β.hom (.up ℤ)).app X ≫
            (Functor.mapHomotopyCategoryCompIso (Iso.refl (f₁ ⋙ v)) (.up ℤ)).inv.app X)) := by
    rw [reassoc_of% h₁, h₂']
    simp only [Category.assoc]
    rw [reassoc_of% h₃']
    simp only [Functor.map_comp, Category.assoc] at h₄ ⊢
    rw [h₄, Iso.inv_hom_id_app_assoc]
  -- the right hand side
  have k₁ := adj₁.mapDerivedCategoryAdjunction_unit_app_Qh_obj X
  have k₁' : adj₁.mapDerivedCategoryAdjunction.unit.app (DerivedCategory.Qh.obj X) =
      DerivedCategory.Qh.map ((adj₁.mapHomotopyCategory (.up ℤ)).unit.app X) ≫
        g₁.mapDerivedCategoryFactorsh.inv.app _ ≫
        g₁.mapDerivedCategory.map (f₁.mapDerivedCategoryFactorsh.inv.app _) := by
    rw [← k₁]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
    rw [← Functor.map_comp, Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  have k₂ := u.mapDerivedCategoryFactorsh.inv.naturality
    ((adj₁.mapHomotopyCategory (.up ℤ)).unit.app X)
  have k₃ : u.mapDerivedCategory.map (g₁.mapDerivedCategory.map
      (f₁.mapDerivedCategoryFactorsh.inv.app X)) ≫
      (Functor.mapDerivedCategorySquareIso τ).hom.app
        (f₁.mapDerivedCategory.obj (DerivedCategory.Qh.obj X)) =
      (Functor.mapDerivedCategorySquareIso τ).hom.app _ ≫
        g₂.mapDerivedCategory.map (v.mapDerivedCategory.map
          (f₁.mapDerivedCategoryFactorsh.inv.app X)) :=
    (Functor.mapDerivedCategorySquareIso τ).hom.naturality _
  have k₄ := Functor.mapDerivedCategorySquareIso_hom_app_Qh_obj τ
    ((f₁.mapHomotopyCategory (.up ℤ)).obj X)
  dsimp only [Functor.comp_obj, Functor.comp_map] at k₂
  have hR : u.mapDerivedCategoryFactorsh.inv.app X ≫
      u.mapDerivedCategory.map
        (adj₁.mapDerivedCategoryAdjunction.unit.app (DerivedCategory.Qh.obj X)) ≫
      (Functor.mapDerivedCategorySquareIso τ).hom.app
        (f₁.mapDerivedCategory.obj (DerivedCategory.Qh.obj X)) ≫
      g₂.mapDerivedCategory.map (v.mapDerivedCategory.map
        (f₁.mapDerivedCategoryFactorsh.hom.app X)) ≫
      g₂.mapDerivedCategory.map (v.mapDerivedCategoryFactorsh.hom.app
        ((f₁.mapHomotopyCategory (.up ℤ)).obj X)) ≫
      g₂.mapDerivedCategoryFactorsh.hom.app
        ((v.mapHomotopyCategory (.up ℤ)).obj ((f₁.mapHomotopyCategory (.up ℤ)).obj X)) =
      DerivedCategory.Qh.map ((u.mapHomotopyCategory (.up ℤ)).map
        ((adj₁.mapHomotopyCategory (.up ℤ)).unit.app X) ≫
          (Functor.mapHomotopyCategoryCompIso (Iso.refl (g₁ ⋙ u)) (.up ℤ)).hom.app _ ≫
          (NatTrans.mapHomotopyCategory τ.hom (.up ℤ)).app _ ≫
          (Functor.mapHomotopyCategoryCompIso (Iso.refl (v ⋙ g₂)) (.up ℤ)).inv.app _) := by
    rw [k₁']
    simp only [Functor.map_comp, Category.assoc]
    have hc : g₂.mapDerivedCategory.map (v.mapDerivedCategory.map
        (f₁.mapDerivedCategoryFactorsh.inv.app X)) ≫
        g₂.mapDerivedCategory.map (v.mapDerivedCategory.map
          (f₁.mapDerivedCategoryFactorsh.hom.app X)) = 𝟙 _ := by
      rw [← Functor.map_comp, ← Functor.map_comp, Iso.inv_hom_id_app]
      erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    rw [← reassoc_of% k₂, reassoc_of% k₃, reassoc_of% hc]
    simp only [Functor.map_comp] at k₄ ⊢
    rw [k₄]
  simp only [Category.assoc]
  rw [hL, hR]
  congr 1
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  have hu₂ : (adj₂.mapHomotopyCategory (.up ℤ)).unit.app ((u.mapHomotopyCategory (.up ℤ)).obj
      ((HomotopyCategory.quotient C₁ (.up ℤ)).obj K)) =
      (HomotopyCategory.quotient C₂ (.up ℤ)).map ((adj₂.mapHomologicalComplex (.up ℤ)).unit.app
        ((u.mapHomologicalComplex (.up ℤ)).obj K)) :=
    mapHomotopyCategory_unit_app_quotient _ adj₂ _
  rw [mapHomotopyCategory_unit_app_quotient, hu₂]
  have hc : (adj₂.mapHomologicalComplex (.up ℤ)).unit.app
      ((u.mapHomologicalComplex (.up ℤ)).obj K) ≫
      (g₂.mapHomologicalComplex (.up ℤ)).map
        ((Functor.mapHomologicalComplexCompIso (Iso.refl (u ⋙ f₂)) (.up ℤ)).hom.app K ≫
          (NatTrans.mapHomologicalComplex β.hom (.up ℤ)).app K ≫
          (Functor.mapHomologicalComplexCompIso (Iso.refl (f₁ ⋙ v)) (.up ℤ)).inv.app K) =
      (u.mapHomologicalComplex (.up ℤ)).map ((adj₁.mapHomologicalComplex (.up ℤ)).unit.app K) ≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (g₁ ⋙ u)) (.up ℤ)).hom.app _ ≫
        (NatTrans.mapHomologicalComplex τ.hom (.up ℤ)).app _ ≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (v ⋙ g₂)) (.up ℤ)).inv.app _ := by
    ext n
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      mapHomologicalComplex_unit_app_f, Functor.mapHomologicalComplexCompIso_hom_app_f,
      Functor.mapHomologicalComplexCompIso_inv_app_f, NatTrans.mapHomologicalComplex_app_f,
      Iso.refl_hom, Iso.refl_inv, NatTrans.id_app]
    erw [Category.id_comp, Category.id_comp, Category.comp_id, Category.comp_id]
    exact hβ (K.X n)
  have := (HomotopyCategory.quotient C₂ (.up ℤ)).congr_map hc
  simp only [Functor.map_comp] at this ⊢
  exact this

include adj₁ adj₂ in
/-- **The functors induced on derived categories preserve mates**: if `β : u ⋙ f₂ ≅ f₁ ⋙ v` is
the mate of `τ : g₁ ⋙ u ≅ v ⋙ g₂` for the adjunctions `f₁ ⊣ g₁` and `f₂ ⊣ g₂` of exact
functors, then the isomorphism induced by `β` on derived categories is the mate of the one
induced by `τ`, for the levelwise derived adjunctions `D(f₁) ⊣ D(g₁)` and `D(f₂) ⊣ D(g₂)`. -/
lemma mapDerivedCategoryAdjunction_mate
    (hβ : ∀ K, adj₂.unit.app (u.obj K) ≫ g₂.map (β.hom.app K) =
      u.map (adj₁.unit.app K) ≫ τ.hom.app (f₁.obj K))
    (K : DerivedCategory C₁) :
    adj₂.mapDerivedCategoryAdjunction.unit.app (u.mapDerivedCategory.obj K) ≫
        g₂.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso β).hom.app K) =
      u.mapDerivedCategory.map (adj₁.mapDerivedCategoryAdjunction.unit.app K) ≫
        (Functor.mapDerivedCategorySquareIso τ).hom.app (f₁.mapDerivedCategory.obj K) := by
  have := Localization.essSurj (DerivedCategory.Qh (C := C₁)) (HomotopyCategory.quasiIso C₁ (.up ℤ))
  let e := DerivedCategory.Qh.objObjPreimageIso K
  rw [← cancel_epi (u.mapDerivedCategory.map e.hom)]
  have h₁ : u.mapDerivedCategory.map e.hom ≫
      adj₂.mapDerivedCategoryAdjunction.unit.app (u.mapDerivedCategory.obj K) =
      adj₂.mapDerivedCategoryAdjunction.unit.app (u.mapDerivedCategory.obj _) ≫
        g₂.mapDerivedCategory.map (f₂.mapDerivedCategory.map (u.mapDerivedCategory.map e.hom)) :=
    adj₂.mapDerivedCategoryAdjunction.unit.naturality _
  have h₂ : f₂.mapDerivedCategory.map (u.mapDerivedCategory.map e.hom) ≫
      (Functor.mapDerivedCategorySquareIso β).hom.app K =
      (Functor.mapDerivedCategorySquareIso β).hom.app _ ≫
        v.mapDerivedCategory.map (f₁.mapDerivedCategory.map e.hom) :=
    (Functor.mapDerivedCategorySquareIso β).hom.naturality _
  have h₃ : e.hom ≫ adj₁.mapDerivedCategoryAdjunction.unit.app K =
      adj₁.mapDerivedCategoryAdjunction.unit.app _ ≫
        g₁.mapDerivedCategory.map (f₁.mapDerivedCategory.map e.hom) :=
    adj₁.mapDerivedCategoryAdjunction.unit.naturality _
  have h₄ : u.mapDerivedCategory.map (g₁.mapDerivedCategory.map
      (f₁.mapDerivedCategory.map e.hom)) ≫
      (Functor.mapDerivedCategorySquareIso τ).hom.app (f₁.mapDerivedCategory.obj K) =
      (Functor.mapDerivedCategorySquareIso τ).hom.app _ ≫
        g₂.mapDerivedCategory.map (v.mapDerivedCategory.map (f₁.mapDerivedCategory.map e.hom)) :=
    (Functor.mapDerivedCategorySquareIso τ).hom.naturality _
  rw [reassoc_of% h₁, ← Functor.map_comp, h₂, Functor.map_comp, ← Functor.map_comp_assoc, h₃,
    Functor.map_comp, Category.assoc, h₄,
    reassoc_of% (mapDerivedCategoryAdjunction_mate_Qh_obj adj₁ adj₂ τ β hβ _)]


end Adjunction

namespace Adjunction

section Triangle

variable {C D₁ D₂ : Type*} [Category C] [Category D₁] [Category D₂]
  [Abelian C] [Abelian D₁] [Abelian D₂]
  [MonoidalCategory C] [MonoidalPreadditive C] [HasCountableCoproducts C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C]
  [HasDerivedCategory C] [HasDerivedCategory D₁] [HasDerivedCategory D₂]
  [HasKInjectiveResolutions D₁] [HasKInjectiveResolutions D₂]
  {f₁ : C ⥤ D₁} {g₁ : D₁ ⥤ C} (adj₁ : f₁ ⊣ g₁) {f₂ : C ⥤ D₂} {g₂ : D₂ ⥤ C}
  (adj₂ : f₂ ⊣ g₂) {v : D₁ ⥤ D₂}
  [f₁.Additive] [PreservesFiniteLimits f₁] [PreservesFiniteColimits f₁]
  [g₁.Additive] [PreservesFiniteLimits g₁] [PreservesFiniteColimits g₁]
  [f₂.Additive] [PreservesFiniteLimits f₂] [PreservesFiniteColimits f₂]
  [g₂.Additive] [PreservesFiniteLimits g₂] [PreservesFiniteColimits g₂]
  [v.Additive] [PreservesFiniteLimits v] [PreservesFiniteColimits v]
  (τ : g₁ ≅ v ⋙ g₂) (β : f₂ ≅ f₁ ⋙ v)

include adj₁ adj₂ in
lemma mapDerivedCategoryAdjunction_mate_Qh_obj'
    (hβ : ∀ K, adj₂.unit.app K ≫ g₂.map (β.hom.app K) =
      adj₁.unit.app K ≫ τ.hom.app (f₁.obj K))
    (X : HomotopyCategory C (.up ℤ)) :
    adj₂.mapDerivedCategoryAdjunction.unit.app (DerivedCategory.Qh.obj X) ≫
        g₂.mapDerivedCategory.map
          ((Functor.mapDerivedCategoryTriangleIso β).hom.app (DerivedCategory.Qh.obj X)) =
      adj₁.mapDerivedCategoryAdjunction.unit.app (DerivedCategory.Qh.obj X) ≫
        (Functor.mapDerivedCategoryTriangleIso τ).hom.app
          (f₁.mapDerivedCategory.obj (DerivedCategory.Qh.obj X)) := by
  rw [← cancel_mono (g₂.mapDerivedCategory.map (v.mapDerivedCategory.map
      (f₁.mapDerivedCategoryFactorsh.hom.app X)) ≫
      g₂.mapDerivedCategory.map (v.mapDerivedCategoryFactorsh.hom.app
        ((f₁.mapHomotopyCategory (.up ℤ)).obj X)) ≫
      g₂.mapDerivedCategoryFactorsh.hom.app
        ((v.mapHomotopyCategory (.up ℤ)).obj ((f₁.mapHomotopyCategory (.up ℤ)).obj X)))]
  -- the left hand side
  have h₂ := adj₂.mapDerivedCategoryAdjunction_unit_app_Qh_obj X
  have h₃ := Functor.mapDerivedCategoryTriangleIso_hom_app_Qh_obj β X
  have h₄ := g₂.mapDerivedCategoryFactorsh.hom.naturality
    ((NatTrans.mapHomotopyCategory β.hom (.up ℤ)).app X ≫
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (f₁ ⋙ v)) (.up ℤ)).inv.app X)
  dsimp only [Functor.comp_obj, Functor.comp_map] at h₄
  have h₂' : adj₂.mapDerivedCategoryAdjunction.unit.app (DerivedCategory.Qh.obj X) =
      DerivedCategory.Qh.map ((adj₂.mapHomotopyCategory (.up ℤ)).unit.app X) ≫
        g₂.mapDerivedCategoryFactorsh.inv.app _ ≫
        g₂.mapDerivedCategory.map (f₂.mapDerivedCategoryFactorsh.inv.app _) := by
    rw [← h₂]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
    rw [← Functor.map_comp, Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  have h₃' := congrArg g₂.mapDerivedCategory.map h₃
  simp only [Functor.map_comp] at h₃'
  have hL : adj₂.mapDerivedCategoryAdjunction.unit.app (DerivedCategory.Qh.obj X) ≫
      g₂.mapDerivedCategory.map
        ((Functor.mapDerivedCategoryTriangleIso β).hom.app (DerivedCategory.Qh.obj X)) ≫
      g₂.mapDerivedCategory.map (v.mapDerivedCategory.map
        (f₁.mapDerivedCategoryFactorsh.hom.app X)) ≫
      g₂.mapDerivedCategory.map (v.mapDerivedCategoryFactorsh.hom.app
        ((f₁.mapHomotopyCategory (.up ℤ)).obj X)) ≫
      g₂.mapDerivedCategoryFactorsh.hom.app
        ((v.mapHomotopyCategory (.up ℤ)).obj ((f₁.mapHomotopyCategory (.up ℤ)).obj X)) =
      DerivedCategory.Qh.map ((adj₂.mapHomotopyCategory (.up ℤ)).unit.app X ≫
        (g₂.mapHomotopyCategory (.up ℤ)).map
          ((NatTrans.mapHomotopyCategory β.hom (.up ℤ)).app X ≫
            (Functor.mapHomotopyCategoryCompIso (Iso.refl (f₁ ⋙ v)) (.up ℤ)).inv.app X)) := by
    rw [h₂']
    simp only [Category.assoc]
    rw [reassoc_of% h₃']
    simp only [Functor.map_comp, Category.assoc] at h₄ ⊢
    rw [h₄, Iso.inv_hom_id_app_assoc]
  -- the right hand side
  have k₁ := adj₁.mapDerivedCategoryAdjunction_unit_app_Qh_obj X
  have k₁' : adj₁.mapDerivedCategoryAdjunction.unit.app (DerivedCategory.Qh.obj X) =
      DerivedCategory.Qh.map ((adj₁.mapHomotopyCategory (.up ℤ)).unit.app X) ≫
        g₁.mapDerivedCategoryFactorsh.inv.app _ ≫
        g₁.mapDerivedCategory.map (f₁.mapDerivedCategoryFactorsh.inv.app _) := by
    rw [← k₁]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
    rw [← Functor.map_comp, Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  have k₃ : g₁.mapDerivedCategory.map (f₁.mapDerivedCategoryFactorsh.inv.app X) ≫
      (Functor.mapDerivedCategoryTriangleIso τ).hom.app
        (f₁.mapDerivedCategory.obj (DerivedCategory.Qh.obj X)) =
      (Functor.mapDerivedCategoryTriangleIso τ).hom.app _ ≫
        g₂.mapDerivedCategory.map (v.mapDerivedCategory.map
          (f₁.mapDerivedCategoryFactorsh.inv.app X)) :=
    (Functor.mapDerivedCategoryTriangleIso τ).hom.naturality _
  have k₄ := Functor.mapDerivedCategoryTriangleIso_hom_app_Qh_obj τ
    ((f₁.mapHomotopyCategory (.up ℤ)).obj X)
  have hR : adj₁.mapDerivedCategoryAdjunction.unit.app (DerivedCategory.Qh.obj X) ≫
      (Functor.mapDerivedCategoryTriangleIso τ).hom.app
        (f₁.mapDerivedCategory.obj (DerivedCategory.Qh.obj X)) ≫
      g₂.mapDerivedCategory.map (v.mapDerivedCategory.map
        (f₁.mapDerivedCategoryFactorsh.hom.app X)) ≫
      g₂.mapDerivedCategory.map (v.mapDerivedCategoryFactorsh.hom.app
        ((f₁.mapHomotopyCategory (.up ℤ)).obj X)) ≫
      g₂.mapDerivedCategoryFactorsh.hom.app
        ((v.mapHomotopyCategory (.up ℤ)).obj ((f₁.mapHomotopyCategory (.up ℤ)).obj X)) =
      DerivedCategory.Qh.map ((adj₁.mapHomotopyCategory (.up ℤ)).unit.app X ≫
          (NatTrans.mapHomotopyCategory τ.hom (.up ℤ)).app _ ≫
          (Functor.mapHomotopyCategoryCompIso (Iso.refl (v ⋙ g₂)) (.up ℤ)).inv.app _) := by
    rw [k₁']
    simp only [Functor.map_comp, Category.assoc]
    have hc : g₂.mapDerivedCategory.map (v.mapDerivedCategory.map
        (f₁.mapDerivedCategoryFactorsh.inv.app X)) ≫
        g₂.mapDerivedCategory.map (v.mapDerivedCategory.map
          (f₁.mapDerivedCategoryFactorsh.hom.app X)) = 𝟙 _ := by
      rw [← Functor.map_comp, ← Functor.map_comp, Iso.inv_hom_id_app]
      erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    rw [reassoc_of% k₃, reassoc_of% hc]
    simp only [Functor.map_comp] at k₄ ⊢
    rw [k₄]
  simp only [Category.assoc]
  rw [hL, hR]
  congr 1
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  rw [mapHomotopyCategory_unit_app_quotient, mapHomotopyCategory_unit_app_quotient]
  have hc : (adj₂.mapHomologicalComplex (.up ℤ)).unit.app K ≫
      (g₂.mapHomologicalComplex (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex β.hom (.up ℤ)).app K ≫
          (Functor.mapHomologicalComplexCompIso (Iso.refl (f₁ ⋙ v)) (.up ℤ)).inv.app K) =
      (adj₁.mapHomologicalComplex (.up ℤ)).unit.app K ≫
        (NatTrans.mapHomologicalComplex τ.hom (.up ℤ)).app _ ≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (v ⋙ g₂)) (.up ℤ)).inv.app _ := by
    ext n
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      mapHomologicalComplex_unit_app_f, Functor.mapHomologicalComplexCompIso_inv_app_f,
      NatTrans.mapHomologicalComplex_app_f, Iso.refl_inv, NatTrans.id_app]
    erw [Category.comp_id, Category.comp_id]
    exact hβ (K.X n)
  have := (HomotopyCategory.quotient C (.up ℤ)).congr_map hc
  simp only [Functor.map_comp] at this ⊢
  exact this

include adj₁ adj₂ in
/-- The form of `CategoryTheory.Adjunction.mapDerivedCategoryAdjunction_mate` for triangles: if
`β : f₂ ≅ f₁ ⋙ v` is the mate of `τ : g₁ ≅ v ⋙ g₂`, then so are the induced isomorphisms on
derived categories. -/
lemma mapDerivedCategoryAdjunction_mate'
    (hβ : ∀ K, adj₂.unit.app K ≫ g₂.map (β.hom.app K) =
      adj₁.unit.app K ≫ τ.hom.app (f₁.obj K))
    (K : DerivedCategory C) :
    adj₂.mapDerivedCategoryAdjunction.unit.app K ≫
        g₂.mapDerivedCategory.map ((Functor.mapDerivedCategoryTriangleIso β).hom.app K) =
      adj₁.mapDerivedCategoryAdjunction.unit.app K ≫
        (Functor.mapDerivedCategoryTriangleIso τ).hom.app (f₁.mapDerivedCategory.obj K) := by
  have := Localization.essSurj (DerivedCategory.Qh (C := C)) (HomotopyCategory.quasiIso C (.up ℤ))
  let e := DerivedCategory.Qh.objObjPreimageIso K
  rw [← cancel_epi e.hom]
  have h₁ : e.hom ≫ adj₂.mapDerivedCategoryAdjunction.unit.app K =
      adj₂.mapDerivedCategoryAdjunction.unit.app _ ≫
        g₂.mapDerivedCategory.map (f₂.mapDerivedCategory.map e.hom) :=
    adj₂.mapDerivedCategoryAdjunction.unit.naturality _
  have h₂ : f₂.mapDerivedCategory.map e.hom ≫
      (Functor.mapDerivedCategoryTriangleIso β).hom.app K =
      (Functor.mapDerivedCategoryTriangleIso β).hom.app _ ≫
        v.mapDerivedCategory.map (f₁.mapDerivedCategory.map e.hom) :=
    (Functor.mapDerivedCategoryTriangleIso β).hom.naturality _
  have h₃ : e.hom ≫ adj₁.mapDerivedCategoryAdjunction.unit.app K =
      adj₁.mapDerivedCategoryAdjunction.unit.app _ ≫
        g₁.mapDerivedCategory.map (f₁.mapDerivedCategory.map e.hom) :=
    adj₁.mapDerivedCategoryAdjunction.unit.naturality _
  have h₄ : g₁.mapDerivedCategory.map (f₁.mapDerivedCategory.map e.hom) ≫
      (Functor.mapDerivedCategoryTriangleIso τ).hom.app (f₁.mapDerivedCategory.obj K) =
      (Functor.mapDerivedCategoryTriangleIso τ).hom.app _ ≫
        g₂.mapDerivedCategory.map (v.mapDerivedCategory.map (f₁.mapDerivedCategory.map e.hom)) :=
    (Functor.mapDerivedCategoryTriangleIso τ).hom.naturality _
  rw [reassoc_of% h₁, ← Functor.map_comp, h₂, Functor.map_comp, reassoc_of% h₃, h₄,
    reassoc_of% (mapDerivedCategoryAdjunction_mate_Qh_obj' adj₁ adj₂ τ β hβ _)]

end Triangle
end Adjunction

end CategoryTheory

section

/-!
# Mates and the functors induced on derived categories

Let `adj₁ : f₁ ⊣ g₁` and `adj₂ : f₂ ⊣ g₂` be adjunctions of exact functors, and let
`β : u ⋙ f₂ ≅ f₁ ⋙ v` be the mate of `τ : g₁ ⋙ u ≅ v ⋙ g₂` for exact `u` and `v`. Then the
isomorphism induced by `β` on derived categories is the mate of the one induced by `τ`, for the
levelwise derived adjunctions `D(f₁) ⊣ D(g₁)` and `D(f₂) ⊣ D(g₂)`
(`CategoryTheory.Adjunction.mapDerivedCategoryAdjunction_mate`).
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory Abelian

namespace CategoryTheory

namespace Functor

section NatIso

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D] [HasDerivedCategory C]
  [HasDerivedCategory D] {F G H : C ⥤ D} [F.Additive] [PreservesFiniteLimits F]
  [PreservesFiniteColimits F] [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]







end NatIso

section DerivedCoherence

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

section Factors

variable {C D E : Type*} [Category C] [Category D] [Category E]
  [Abelian C] [Abelian D] [Abelian E]
  (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]

/-- The composition isomorphism `Functor.mapHomologicalComplexCompIso` of the identity
isomorphism of `F ⋙ G` is the identity. -/
lemma mapHomologicalComplexCompIso_refl_hom_app {ι : Type*} (c : ComplexShape ι)
    (K : HomologicalComplex C c) :
    (mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) c).hom.app K = 𝟙 _ := by
  ext n
  simp

variable [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- The form of `Functor.mapDerivedCategoryCompIso_fac` in which the comparison isomorphism
`Functor.mapHomologicalComplexCompIso`, an identity, has been cancelled. -/
@[reassoc]
lemma mapDerivedCategoryCompIso_hom_app_factors (K : CochainComplex C ℤ) :
    (mapDerivedCategoryCompIso F G).inv.app (DerivedCategory.Q.obj K) ≫
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
      G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) =
    (F ⋙ G).mapDerivedCategoryFactors.hom.app K := by
  rw [← mapDerivedCategoryCompIso_fac, mapHomologicalComplexCompIso_refl_hom_app]
  simp

/-- The form of `Functor.mapDerivedCategoryCompIso_fach` in which the comparison isomorphism
`Functor.mapHomotopyCategoryCompIso`, an identity, has been cancelled. -/
@[reassoc]
lemma mapDerivedCategoryCompIso_hom_app_factorsh
    (K : HomotopyCategory C (ComplexShape.up ℤ)) :
    (mapDerivedCategoryCompIso F G).inv.app (DerivedCategory.Qh.obj K) ≫
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.hom.app K) ≫
      G.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) =
    (F ⋙ G).mapDerivedCategoryFactorsh.hom.app K := by
  rw [← mapDerivedCategoryCompIso_fach, mapHomotopyCategoryCompIso_refl_hom_app (F := F) (G := G)]
  simp

end Factors

section Coherence

variable {C D E E' : Type*} [Category C] [Category D] [Category E] [Category E']
  [Abelian C] [Abelian D] [Abelian E] [Abelian E']
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E] [HasDerivedCategory E']

variable (C) in
/-- On the image of an object of the homotopy category, the isomorphism
`Functor.mapDerivedCategoryIdIso` is the factorization `Functor.mapDerivedCategoryFactorsh` of
the identity functor. -/
lemma mapDerivedCategoryIdIso_hom_app_Qh_obj (K : HomotopyCategory C (ComplexShape.up ℤ)) :
    (mapDerivedCategoryIdIso C).hom.app (DerivedCategory.Qh.obj K) =
      (𝟭 C).mapDerivedCategoryFactorsh.hom.app K := by
  have h := congr_app (congr_arg Iso.hom (mapDerivedCategoryIdIso_factorsh C)) K
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.rightUnitor_hom_app, isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app] at h
  have hq : DerivedCategory.Qh.map ((mapHomotopyCategoryIdIso C (ComplexShape.up ℤ)).hom.app K) =
      𝟙 (((𝟭 C).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).obj K) := by
    rw [mapHomotopyCategoryIdIso_hom_app_eq_id]
    exact DerivedCategory.Qh.map_id _
  refine (Category.comp_id _).symm.trans (h.trans ?_)
  rw [hq]
  -- the identities are those of objects which agree only up to unfolding `𝟭 C`
  erw [Category.id_comp, Category.comp_id]

variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The left unit law for `Functor.mapDerivedCategoryCompIso`. -/
lemma mapDerivedCategoryCompIso_id_comp :
    (mapDerivedCategoryCompIso (𝟭 C) F).inv ≫
        Functor.whiskerRight (mapDerivedCategoryIdIso C).hom F.mapDerivedCategory =
      𝟙 F.mapDerivedCategory := by
  refine Localization.natTrans_ext DerivedCategory.Qh
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) (fun K => ?_)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, NatTrans.id_app]
  rw [← cancel_mono (F.mapDerivedCategoryFactorsh.hom.app K),
    mapDerivedCategoryIdIso_hom_app_Qh_obj, Category.assoc]
  exact (mapDerivedCategoryCompIso_hom_app_factorsh (𝟭 C) F K).trans
    (Category.id_comp _).symm

/-- The right unit law for `Functor.mapDerivedCategoryCompIso`. -/
lemma mapDerivedCategoryCompIso_comp_id :
    (mapDerivedCategoryCompIso F (𝟭 D)).inv ≫
        Functor.whiskerLeft F.mapDerivedCategory (mapDerivedCategoryIdIso D).hom =
      𝟙 F.mapDerivedCategory := by
  refine Localization.natTrans_ext DerivedCategory.Qh
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) (fun K => ?_)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, NatTrans.id_app]
  have hnat : (mapDerivedCategoryIdIso D).hom.app
        (F.mapDerivedCategory.obj (DerivedCategory.Qh.obj K)) ≫
      F.mapDerivedCategoryFactorsh.hom.app K =
      (𝟭 D).mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.hom.app K) ≫
        (mapDerivedCategoryIdIso D).hom.app
          (DerivedCategory.Qh.obj ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K)) :=
    ((mapDerivedCategoryIdIso D).hom.naturality _).symm
  rw [← cancel_mono (F.mapDerivedCategoryFactorsh.hom.app K), Category.assoc, hnat,
    mapDerivedCategoryIdIso_hom_app_Qh_obj]
  exact (mapDerivedCategoryCompIso_hom_app_factorsh F (𝟭 D) K).trans
    (Category.id_comp _).symm

variable (G : D ⥤ E) (H : E ⥤ E') [G.Additive] [H.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]

/-- The associativity law for `Functor.mapDerivedCategoryCompIso`: the two ways of comparing
`D(F ⋙ G ⋙ H)` with `D(F) ⋙ D(G) ⋙ D(H)` agree. -/
lemma mapDerivedCategoryCompIso_assoc :
    (mapDerivedCategoryCompIso F (G ⋙ H)).inv ≫
        Functor.whiskerLeft F.mapDerivedCategory (mapDerivedCategoryCompIso G H).inv =
      (mapDerivedCategoryCompIso (F ⋙ G) H).inv ≫
        Functor.whiskerRight (mapDerivedCategoryCompIso F G).inv H.mapDerivedCategory := by
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) (fun K => ?_)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  have hnat : (mapDerivedCategoryCompIso G H).inv.app
        (F.mapDerivedCategory.obj (DerivedCategory.Q.obj K)) ≫
      H.mapDerivedCategory.map (G.mapDerivedCategory.map
        (F.mapDerivedCategoryFactors.hom.app K)) =
      (G ⋙ H).mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
        (mapDerivedCategoryCompIso G H).inv.app
          (DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) :=
    ((mapDerivedCategoryCompIso G H).inv.naturality _).symm
  rw [← cancel_mono (H.mapDerivedCategory.map (G.mapDerivedCategory.map
      (F.mapDerivedCategoryFactors.hom.app K)) ≫
    H.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
    H.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)))]
  trans (F ⋙ G ⋙ H).mapDerivedCategoryFactors.hom.app K
  · rw [Category.assoc, reassoc_of% hnat,
      mapDerivedCategoryCompIso_hom_app_factors G H
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)]
    exact mapDerivedCategoryCompIso_hom_app_factors F (G ⋙ H) K
  · symm
    rw [Category.assoc]
    simp only [← Functor.map_comp_assoc]
    rw [mapDerivedCategoryCompIso_hom_app_factors F G K]
    exact mapDerivedCategoryCompIso_hom_app_factors (F ⋙ G) H K

end Coherence

section Whisker

variable {C D E : Type*} [Category C] [Category D] [Category E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]

/-- The composition isomorphism `Functor.mapDerivedCategoryCompIso` is natural in the first
functor. -/
lemma mapDerivedCategoryNatIso_isoWhiskerRight {F F' : C ⥤ D} [F.Additive] [F'.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F'] (e : F ≅ F') (G : D ⥤ E)
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    (mapDerivedCategoryNatIso (isoWhiskerRight e G)).hom ≫ (mapDerivedCategoryCompIso F' G).inv =
      (mapDerivedCategoryCompIso F G).inv ≫
        Functor.whiskerRight (mapDerivedCategoryNatIso e).hom G.mapDerivedCategory := by
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) (fun K => ?_)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app]
  rw [← cancel_mono (G.mapDerivedCategory.map (F'.mapDerivedCategoryFactors.hom.app K) ≫
      G.mapDerivedCategoryFactors.hom.app ((F'.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)),
    Category.assoc, mapDerivedCategoryCompIso_hom_app_factors, mapDerivedCategoryNatIso_fac,
    Category.assoc, ← Functor.map_comp_assoc, mapDerivedCategoryNatIso_fac, Functor.map_comp_assoc,
    mapDerivedCategoryFactors_hom_naturality, mapDerivedCategoryCompIso_hom_app_factors_assoc]
  congr 2

/-- The composition isomorphism `Functor.mapDerivedCategoryCompIso` is natural in the second
functor. -/
lemma mapDerivedCategoryNatIso_isoWhiskerLeft (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] {G G' : D ⥤ E} [G.Additive]
    [G'.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits G'] [PreservesFiniteColimits G'] (e : G ≅ G') :
    (mapDerivedCategoryNatIso (isoWhiskerLeft F e)).hom ≫ (mapDerivedCategoryCompIso F G').inv =
      (mapDerivedCategoryCompIso F G).inv ≫
        Functor.whiskerLeft F.mapDerivedCategory (mapDerivedCategoryNatIso e).hom := by
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) (fun K => ?_)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
  rw [← cancel_mono (G'.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
      G'.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)),
    Category.assoc, mapDerivedCategoryCompIso_hom_app_factors, mapDerivedCategoryNatIso_fac,
    Category.assoc, ← reassoc_of% ((mapDerivedCategoryNatIso e).hom.naturality
      (F.mapDerivedCategoryFactors.hom.app K)), mapDerivedCategoryNatIso_fac,
    mapDerivedCategoryCompIso_hom_app_factors_assoc]
  congr 2

end Whisker

end DerivedCoherence

variable {A B B' E : Type*} [Category A] [Category B] [Category B'] [Category E] [Abelian A]
  [Abelian B] [Abelian B'] [Abelian E] [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory B'] [HasDerivedCategory E]
  {F₁ : A ⥤ B} {F₂ : B ⥤ E} {G₁ : A ⥤ B'} {G₂ : B' ⥤ E}
  [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  [G₁.Additive] [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
  [G₂.Additive] [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]






section Triangle

variable {A B E : Type*} [Category A] [Category B] [Category E] [Abelian A] [Abelian B]
  [Abelian E] [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory E]
  {F₁ : A ⥤ B} {G₁ : B ⥤ E} {F₂ : A ⥤ E}
  [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [G₁.Additive] [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
  [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]





end Triangle
end Functor

namespace Adjunction

variable {C₁ D₁ C₂ D₂ : Type*} [Category C₁] [Category D₁] [Category C₂] [Category D₂]
  [Abelian C₁] [Abelian D₁] [Abelian C₂] [Abelian D₂]
  [MonoidalCategory C₁] [MonoidalPreadditive C₁] [HasCountableCoproducts C₁]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C₁), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C₁), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C₁), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ C₁] [HasExactColimitsOfShape ℤ C₁]
  [∀ (X : C₁), PreservesColimitsOfShape ℤ ((curriedTensor C₁).obj X)]
  [∀ (X : C₁), PreservesColimitsOfShape ℤ ((curriedTensor C₁).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C₁]
  [MonoidalCategory C₂] [MonoidalPreadditive C₂] [HasCountableCoproducts C₂]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C₂), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C₂), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C₂), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ C₂] [HasExactColimitsOfShape ℤ C₂]
  [∀ (X : C₂), PreservesColimitsOfShape ℤ ((curriedTensor C₂).obj X)]
  [∀ (X : C₂), PreservesColimitsOfShape ℤ ((curriedTensor C₂).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C₂]
  [HasDerivedCategory C₁] [HasDerivedCategory D₁] [HasDerivedCategory C₂]
  [HasDerivedCategory D₂] [HasKInjectiveResolutions D₁] [HasKInjectiveResolutions D₂]
  {f₁ : C₁ ⥤ D₁} {g₁ : D₁ ⥤ C₁} (adj₁ : f₁ ⊣ g₁) {f₂ : C₂ ⥤ D₂} {g₂ : D₂ ⥤ C₂}
  (adj₂ : f₂ ⊣ g₂) {u : C₁ ⥤ C₂} {v : D₁ ⥤ D₂}
  [f₁.Additive] [PreservesFiniteLimits f₁] [PreservesFiniteColimits f₁]
  [g₁.Additive] [PreservesFiniteLimits g₁] [PreservesFiniteColimits g₁]
  [f₂.Additive] [PreservesFiniteLimits f₂] [PreservesFiniteColimits f₂]
  [g₂.Additive] [PreservesFiniteLimits g₂] [PreservesFiniteColimits g₂]
  [u.Additive] [PreservesFiniteLimits u] [PreservesFiniteColimits u]
  [v.Additive] [PreservesFiniteLimits v] [PreservesFiniteColimits v]
  (τ : g₁ ⋙ u ≅ v ⋙ g₂) (β : u ⋙ f₂ ≅ f₁ ⋙ v)






end Adjunction

namespace Adjunction

section Triangle

variable {C D₁ D₂ : Type*} [Category C] [Category D₁] [Category D₂]
  [Abelian C] [Abelian D₁] [Abelian D₂]
  [MonoidalCategory C] [MonoidalPreadditive C] [HasCountableCoproducts C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C]
  [HasDerivedCategory C] [HasDerivedCategory D₁] [HasDerivedCategory D₂]
  [HasKInjectiveResolutions D₁] [HasKInjectiveResolutions D₂]
  {f₁ : C ⥤ D₁} {g₁ : D₁ ⥤ C} (adj₁ : f₁ ⊣ g₁) {f₂ : C ⥤ D₂} {g₂ : D₂ ⥤ C}
  (adj₂ : f₂ ⊣ g₂) {v : D₁ ⥤ D₂}
  [f₁.Additive] [PreservesFiniteLimits f₁] [PreservesFiniteColimits f₁]
  [g₁.Additive] [PreservesFiniteLimits g₁] [PreservesFiniteColimits g₁]
  [f₂.Additive] [PreservesFiniteLimits f₂] [PreservesFiniteColimits f₂]
  [g₂.Additive] [PreservesFiniteLimits g₂] [PreservesFiniteColimits g₂]
  [v.Additive] [PreservesFiniteLimits v] [PreservesFiniteColimits v]
  (τ : g₁ ≅ v ⋙ g₂) (β : f₂ ≅ f₁ ⋙ v)





end Triangle
end Adjunction

end CategoryTheory

end
