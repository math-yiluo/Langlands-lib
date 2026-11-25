/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange

/-!
# Functoriality of the base change morphism of bounded below right derived functors

For a square `e : G ⋙ γ ⟶ β ⋙ G'` with `β`, `γ` exact, `Functor.rightDerivedFunctorPlusBaseChange`
is the base change morphism `R⁺G ⋙ γ⁺ ⟶ β⁺ ⋙ R⁺G'`. We record two of its functoriality
properties:

- `Functor.rightDerivedFunctorPlusBaseChange_naturality`: it is natural in the exact functors
  `β` and `γ`, for isomorphisms `γ ≅ γ₂`, `β ≅ β₂` compatible with the squares;
- `Functor.rightDerivedFunctorPlusBaseChange_paste`: the base change morphism of two squares
  pasted along `G'` (`Functor.baseChangePaste`) is the composite of the two base change
  morphisms, modulo `Functor.mapDerivedCategoryPlusCompIso`.

Both are proved by the uniqueness of natural transformations out of a right derived functor
(`Functor.rightDerived_ext`), the base change morphism being computed on complexes by
`Functor.rightDerivedFunctorPlusBaseChange_fac_app`.
-/

@[expose] public section

open CategoryTheory Category Limits

namespace CategoryTheory.NatTrans

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Preadditive C] [Preadditive D] [Preadditive E]

/-- `NatTrans.mapHomotopyCategoryPlus` of a right whiskering is the image of
`NatTrans.mapHomotopyCategoryPlus`, modulo `Functor.mapHomotopyCategoryPlusCompIso`. -/
lemma mapHomotopyCategoryPlusCompIso_whiskerRight_app {F₁ F₂ : C ⥤ D} [F₁.Additive] [F₂.Additive]
    (τ : F₁ ⟶ F₂) (G : D ⥤ E) [G.Additive] (K : HomotopyCategory.Plus C) :
    (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F₁ ⋙ G))).hom.app K ≫
        (NatTrans.mapHomotopyCategoryPlus (Functor.whiskerRight τ G)).app K =
      G.mapHomotopyCategoryPlus.map ((NatTrans.mapHomotopyCategoryPlus τ).app K) ≫
        (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F₂ ⋙ G))).hom.app K := by
  rw [Functor.mapHomotopyCategoryPlusCompIso_refl_hom_app,
    Functor.mapHomotopyCategoryPlusCompIso_refl_hom_app]
  apply (HomotopyCategory.Plus.ι E).map_injective
  obtain ⟨⟨X⟩, hK⟩ := K
  rw [Functor.map_comp, Functor.map_comp, ι_map_mapHomotopyCategoryPlus_app]
  erw [Functor.map_id, Functor.map_id, id_comp, comp_id]
  have h : (HomotopyCategory.Plus.ι E).map (G.mapHomotopyCategoryPlus.map
      ((NatTrans.mapHomotopyCategoryPlus τ).app ⟨⟨X⟩, hK⟩)) =
      (G.mapHomotopyCategory _).map ((HomotopyCategory.Plus.ι D).map
        ((NatTrans.mapHomotopyCategoryPlus τ).app ⟨⟨X⟩, hK⟩)) := rfl
  rw [h, ι_map_mapHomotopyCategoryPlus_app]
  rfl

/-- `NatTrans.mapHomotopyCategoryPlus` of a left whiskering, modulo the composition
isomorphisms `Functor.mapHomotopyCategoryPlusCompIso`. -/
lemma mapHomotopyCategoryPlusCompIso_whiskerLeft_app (F : C ⥤ D) [F.Additive] {G₁ G₂ : D ⥤ E}
    [G₁.Additive] [G₂.Additive] (τ : G₁ ⟶ G₂) (K : HomotopyCategory.Plus C) :
    (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G₁))).hom.app K ≫
        (NatTrans.mapHomotopyCategoryPlus (Functor.whiskerLeft F τ)).app K =
      (NatTrans.mapHomotopyCategoryPlus τ).app (F.mapHomotopyCategoryPlus.obj K) ≫
        (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G₂))).hom.app K := by
  rw [Functor.mapHomotopyCategoryPlusCompIso_refl_hom_app,
    Functor.mapHomotopyCategoryPlusCompIso_refl_hom_app]
  apply (HomotopyCategory.Plus.ι E).map_injective
  obtain ⟨⟨X⟩, hK⟩ := K
  rw [Functor.map_comp, Functor.map_comp, ι_map_mapHomotopyCategoryPlus_app,
    ι_map_mapHomotopyCategoryPlus_app]
  erw [Functor.map_id, Functor.map_id, id_comp, comp_id]
  rfl

variable {E' : Type*} [Category* E'] [Preadditive E']

/-- `NatTrans.mapHomotopyCategoryPlus` sends an associator to the identity. -/
lemma mapHomotopyCategoryPlus_associator_hom_app (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ E')
    [F.Additive] [G.Additive] [H.Additive] (K : HomotopyCategory.Plus C) :
    (NatTrans.mapHomotopyCategoryPlus (Functor.associator F G H).hom).app K = 𝟙 _ := by
  apply (HomotopyCategory.Plus.ι E').map_injective
  obtain ⟨⟨X⟩, hK⟩ := K
  rw [NatTrans.ι_map_mapHomotopyCategoryPlus_app]
  erw [CategoryTheory.Functor.map_id]
  change (HomotopyCategory.quotient _ _).map _ = 𝟙 ((HomotopyCategory.quotient _ _).obj _)
  rw [← (HomotopyCategory.quotient _ _).map_id]
  congr 1

/-- `NatTrans.mapHomotopyCategoryPlus` sends the inverse of an associator to the identity. -/
lemma mapHomotopyCategoryPlus_associator_inv_app (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ E')
    [F.Additive] [G.Additive] [H.Additive] (K : HomotopyCategory.Plus C) :
    (NatTrans.mapHomotopyCategoryPlus (Functor.associator F G H).inv).app K = 𝟙 _ := by
  apply (HomotopyCategory.Plus.ι E').map_injective
  obtain ⟨⟨X⟩, hK⟩ := K
  rw [NatTrans.ι_map_mapHomotopyCategoryPlus_app]
  erw [CategoryTheory.Functor.map_id]
  change (HomotopyCategory.quotient _ _).map _ = 𝟙 ((HomotopyCategory.quotient _ _).obj _)
  rw [← (HomotopyCategory.quotient _ _).map_id]
  congr 1

end CategoryTheory.NatTrans

namespace CategoryTheory.Functor

section

variable {B B' C C' : Type*} [Category* B] [Category* B'] [Category* C] [Category* C']
  [Abelian B] [Abelian B'] [Abelian C] [Abelian C']
  [HasDerivedCategory B] [HasDerivedCategory B'] [HasDerivedCategory C] [HasDerivedCategory C']
  [EnoughInjectives B] [EnoughInjectives B']
  {G : B ⥤ C} {G' : B' ⥤ C'} {β : B ⥤ B'} {γ : C ⥤ C'}
  [G.Additive] [G'.Additive] [β.Additive] [γ.Additive]
  [PreservesFiniteLimits β] [PreservesFiniteColimits β]
  [PreservesFiniteLimits γ] [PreservesFiniteColimits γ]

/-- The base change morphism on the image of a bounded below complex `K`: it is computed by
`e` and the unit of the right derived functor of `G'`. -/
@[reassoc]
lemma rightDerivedFunctorPlusBaseChange_fac_app (e : G ⋙ γ ⟶ β ⋙ G')
    (K : HomotopyCategory.Plus B) :
    γ.mapDerivedCategoryPlus.map (G.rightDerivedFunctorPlusUnith.app K) ≫
        (rightDerivedFunctorPlusBaseChange e).app (DerivedCategory.Plus.Qh.obj K) =
      γ.mapDerivedCategoryPlusFactorsh.hom.app (G.mapHomotopyCategoryPlus.obj K) ≫
        DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus e).app K) ≫
        G'.rightDerivedFunctorPlusUnith.app (β.mapHomotopyCategoryPlus.obj K) ≫
        G'.rightDerivedFunctorPlus.map (β.mapDerivedCategoryPlusFactorsh.inv.app K) := by
  have h := congr_app (rightDerivedFunctorPlusBaseChange_fac e) K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, comp_id] at h
  refine h.trans ?_
  simp only [rightDerivedFunctorPlusBaseChangeAux, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.associator_inv_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.mapHomotopyCategoryPlusCompIso_refl_hom_app,
    Functor.mapHomotopyCategoryPlusCompIso_refl_inv_app, id_comp, comp_id]
  simp

variable {β₂ : B ⥤ B'} {γ₂ : C ⥤ C'} [β₂.Additive] [γ₂.Additive]
  [PreservesFiniteLimits β₂] [PreservesFiniteColimits β₂]
  [PreservesFiniteLimits γ₂] [PreservesFiniteColimits γ₂]

/-- **Naturality of the base change morphism** in the exact functors: if `u : γ ≅ γ₂` and
`v : β ≅ β₂` relate the squares `e` and `e₂`, then the base change morphisms of `e` and `e₂`
are related by the induced isomorphisms `γ⁺ ≅ γ₂⁺` and `β⁺ ≅ β₂⁺`. -/
lemma rightDerivedFunctorPlusBaseChange_naturality (e : G ⋙ γ ⟶ β ⋙ G')
    (e₂ : G ⋙ γ₂ ⟶ β₂ ⋙ G') (u : γ ≅ γ₂) (v : β ≅ β₂)
    (h : e ≫ Functor.whiskerRight v.hom G' = Functor.whiskerLeft G u.hom ≫ e₂)
    (K : DerivedCategory.Plus B) :
    (rightDerivedFunctorPlusBaseChange e).app K ≫
        G'.rightDerivedFunctorPlus.map ((mapDerivedCategoryPlusNatIso v).hom.app K) =
      (mapDerivedCategoryPlusNatIso u).hom.app (G.rightDerivedFunctorPlus.obj K) ≫
        (rightDerivedFunctorPlusBaseChange e₂).app K := by
  suffices key : rightDerivedFunctorPlusBaseChange e ≫
      Functor.whiskerRight (mapDerivedCategoryPlusNatIso v).hom G'.rightDerivedFunctorPlus =
      Functor.whiskerLeft G.rightDerivedFunctorPlus (mapDerivedCategoryPlusNatIso u).hom ≫
        rightDerivedFunctorPlusBaseChange e₂ from congr_app key K
  refine Functor.rightDerived_ext _ (Functor.whiskerRight G.rightDerivedFunctorPlusUnith
    γ.mapDerivedCategoryPlus ≫ (Functor.associator _ _ _).hom)
    (HomotopyCategory.Plus.quasiIso B) _ _ _ (NatTrans.ext (funext fun K => ?_))
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, comp_id, Functor.comp_obj]
  -- the components of `e` and `e₂` on `K`, related by `h`
  have hK : (NatTrans.mapHomotopyCategoryPlus e).app K ≫
      G'.mapHomotopyCategoryPlus.map ((NatTrans.mapHomotopyCategoryPlus v.hom).app K) =
      (NatTrans.mapHomotopyCategoryPlus u.hom).app (G.mapHomotopyCategoryPlus.obj K) ≫
        (NatTrans.mapHomotopyCategoryPlus e₂).app K := by
    have h₁ := congr_app (congrArg NatTrans.mapHomotopyCategoryPlus h) K
    simp only [NatTrans.mapHomotopyCategoryPlus_comp, NatTrans.comp_app] at h₁
    have h₂ := NatTrans.mapHomotopyCategoryPlusCompIso_whiskerRight_app v.hom G' K
    have h₃ := NatTrans.mapHomotopyCategoryPlusCompIso_whiskerLeft_app G u.hom K
    rw [Functor.mapHomotopyCategoryPlusCompIso_refl_hom_app,
      Functor.mapHomotopyCategoryPlusCompIso_refl_hom_app] at h₂ h₃
    erw [id_comp, comp_id] at h₂ h₃
    rw [h₂, h₃] at h₁
    exact h₁
  have hv : β.mapDerivedCategoryPlusFactorsh.inv.app K ≫
      (mapDerivedCategoryPlusNatIso v).hom.app (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus v.hom).app K) ≫
        β₂.mapDerivedCategoryPlusFactorsh.inv.app K := by
    rw [← cancel_epi (β.mapDerivedCategoryPlusFactorsh.hom.app K),
      ← cancel_mono (β₂.mapDerivedCategoryPlusFactorsh.hom.app K)]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app]
    exact (mapDerivedCategoryPlusNatIso_hom_app_factorsh v K).trans (by erw [comp_id])
  have hu := (mapDerivedCategoryPlusNatIso u).hom.naturality
    (G.rightDerivedFunctorPlusUnith.app K)
  have hu' := mapDerivedCategoryPlusNatIso_hom_app_factorsh u (G.mapHomotopyCategoryPlus.obj K)
  have hη := G'.rightDerivedFunctorPlusUnith.naturality
    ((NatTrans.mapHomotopyCategoryPlus v.hom).app K)
  simp only [Functor.comp_obj, Functor.comp_map] at hu hη
  simp only [rightDerivedFunctorPlusBaseChange_fac_app_assoc, reassoc_of% hu,
    rightDerivedFunctorPlusBaseChange_fac_app, reassoc_of% hu']
  simp only [← Functor.map_comp, hv]
  simp only [Functor.map_comp, ← reassoc_of% hη]
  simp only [← Functor.map_comp_assoc, hK]

end

end CategoryTheory.Functor

namespace CategoryTheory.Functor

section Paste

variable {B₁ B₂ B₃ C₁ C₂ C₃ : Type*} [Category* B₁] [Category* B₂] [Category* B₃]
  [Category* C₁] [Category* C₂] [Category* C₃]
  [Abelian B₁] [Abelian B₂] [Abelian B₃] [Abelian C₁] [Abelian C₂] [Abelian C₃]
  [HasDerivedCategory B₁] [HasDerivedCategory B₂] [HasDerivedCategory B₃]
  [HasDerivedCategory C₁] [HasDerivedCategory C₂] [HasDerivedCategory C₃]
  [EnoughInjectives B₁] [EnoughInjectives B₂] [EnoughInjectives B₃]
  {G₁ : B₁ ⥤ C₁} {G₂ : B₂ ⥤ C₂} {G₃ : B₃ ⥤ C₃} {β₁ : B₁ ⥤ B₂} {γ₁ : C₁ ⥤ C₂}
  {β₂ : B₂ ⥤ B₃} {γ₂ : C₂ ⥤ C₃}
  [G₁.Additive] [G₂.Additive] [G₃.Additive] [β₁.Additive] [γ₁.Additive]
  [β₂.Additive] [γ₂.Additive]
  [PreservesFiniteLimits β₁] [PreservesFiniteColimits β₁]
  [PreservesFiniteLimits γ₁] [PreservesFiniteColimits γ₁]
  [PreservesFiniteLimits β₂] [PreservesFiniteColimits β₂]
  [PreservesFiniteLimits γ₂] [PreservesFiniteColimits γ₂]

/-- The pasting of two squares `e₁ : G₁ ⋙ γ₁ ⟶ β₁ ⋙ G₂` and `e₂ : G₂ ⋙ γ₂ ⟶ β₂ ⋙ G₃`
along `G₂`. -/
def baseChangePaste (e₁ : G₁ ⋙ γ₁ ⟶ β₁ ⋙ G₂) (e₂ : G₂ ⋙ γ₂ ⟶ β₂ ⋙ G₃) :
    G₁ ⋙ γ₁ ⋙ γ₂ ⟶ (β₁ ⋙ β₂) ⋙ G₃ :=
  (Functor.associator G₁ γ₁ γ₂).inv ≫ Functor.whiskerRight e₁ γ₂ ≫
    (Functor.associator β₁ G₂ γ₂).hom ≫ Functor.whiskerLeft β₁ e₂ ≫
    (Functor.associator β₁ β₂ G₃).inv

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- **Pasting law for the base change morphism**: the base change morphism of the pasting of
`e₁` and `e₂` is the composite of `γ₂⁺` of the base change morphism of `e₁` with the base
change morphism of `e₂`, modulo the composition isomorphisms of the exact functors. -/
lemma rightDerivedFunctorPlusBaseChange_paste (e₁ : G₁ ⋙ γ₁ ⟶ β₁ ⋙ G₂)
    (e₂ : G₂ ⋙ γ₂ ⟶ β₂ ⋙ G₃) (K : DerivedCategory.Plus B₁) :
    (rightDerivedFunctorPlusBaseChange (baseChangePaste e₁ e₂)).app K ≫
        G₃.rightDerivedFunctorPlus.map ((mapDerivedCategoryPlusCompIso β₁ β₂).hom.app K) =
      (mapDerivedCategoryPlusCompIso γ₁ γ₂).hom.app (G₁.rightDerivedFunctorPlus.obj K) ≫
        γ₂.mapDerivedCategoryPlus.map ((rightDerivedFunctorPlusBaseChange e₁).app K) ≫
        (rightDerivedFunctorPlusBaseChange e₂).app (β₁.mapDerivedCategoryPlus.obj K) := by
  suffices key : rightDerivedFunctorPlusBaseChange (baseChangePaste e₁ e₂) ≫
      Functor.whiskerRight (mapDerivedCategoryPlusCompIso β₁ β₂).hom
        G₃.rightDerivedFunctorPlus =
      Functor.whiskerLeft G₁.rightDerivedFunctorPlus (mapDerivedCategoryPlusCompIso γ₁ γ₂).hom ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (rightDerivedFunctorPlusBaseChange e₁) γ₂.mapDerivedCategoryPlus ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft β₁.mapDerivedCategoryPlus (rightDerivedFunctorPlusBaseChange e₂) ≫
        (Functor.associator _ _ _).inv by
    simpa using congr_app key K
  refine Functor.rightDerived_ext _ (Functor.whiskerRight G₁.rightDerivedFunctorPlusUnith
    (γ₁ ⋙ γ₂).mapDerivedCategoryPlus ≫ (Functor.associator _ _ _).hom)
    (HomotopyCategory.Plus.quasiIso B₁) _ _ _ (NatTrans.ext (funext fun K => ?_))
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, comp_id, id_comp, Functor.comp_obj]
  -- the components of the pasted square
  have hK : (NatTrans.mapHomotopyCategoryPlus (baseChangePaste e₁ e₂)).app K =
      γ₂.mapHomotopyCategoryPlus.map ((NatTrans.mapHomotopyCategoryPlus e₁).app K) ≫
        (NatTrans.mapHomotopyCategoryPlus e₂).app (β₁.mapHomotopyCategoryPlus.obj K) := by
    have h₂ := NatTrans.mapHomotopyCategoryPlusCompIso_whiskerRight_app e₁ γ₂ K
    have h₃ := NatTrans.mapHomotopyCategoryPlusCompIso_whiskerLeft_app β₁ e₂ K
    rw [Functor.mapHomotopyCategoryPlusCompIso_refl_hom_app,
      Functor.mapHomotopyCategoryPlusCompIso_refl_hom_app] at h₂ h₃
    erw [id_comp, comp_id] at h₂ h₃
    simp only [baseChangePaste, NatTrans.mapHomotopyCategoryPlus_comp, NatTrans.comp_app,
      NatTrans.mapHomotopyCategoryPlus_associator_hom_app,
      NatTrans.mapHomotopyCategoryPlus_associator_inv_app]
    erw [id_comp, comp_id, id_comp, h₂, h₃]
  have hβ : (β₁ ⋙ β₂).mapDerivedCategoryPlusFactorsh.inv.app K ≫
      (mapDerivedCategoryPlusCompIso β₁ β₂).hom.app (DerivedCategory.Plus.Qh.obj K) =
      β₂.mapDerivedCategoryPlusFactorsh.inv.app (β₁.mapHomotopyCategoryPlus.obj K) ≫
        β₂.mapDerivedCategoryPlus.map (β₁.mapDerivedCategoryPlusFactorsh.inv.app K) := by
    have h := mapDerivedCategoryPlusCompIso_hom_app_factorsh β₁ β₂ K
    rw [← cancel_epi ((β₁ ⋙ β₂).mapDerivedCategoryPlusFactorsh.hom.app K)]
    simp only [Iso.hom_inv_id_app_assoc]
    simp only [← h, Category.assoc, Iso.hom_inv_id_app_assoc, ← Functor.map_comp,
      Iso.hom_inv_id_app]
    erw [Functor.map_id, comp_id]
  have hγ := mapDerivedCategoryPlusCompIso_hom_app_factorsh γ₁ γ₂
    (G₁.mapHomotopyCategoryPlus.obj K)
  have hn := (mapDerivedCategoryPlusCompIso γ₁ γ₂).hom.naturality
    (G₁.rightDerivedFunctorPlusUnith.app K)
  have hbc := (rightDerivedFunctorPlusBaseChange e₂).naturality
    (β₁.mapDerivedCategoryPlusFactorsh.inv.app K)
  have hf := γ₂.mapDerivedCategoryPlusFactorsh.hom.naturality
    ((NatTrans.mapHomotopyCategoryPlus e₁).app K)
  simp only [Functor.comp_obj, Functor.comp_map] at hn hbc hf
  simp only [rightDerivedFunctorPlusBaseChange_fac_app_assoc, reassoc_of% hn,
    ← Functor.map_comp_assoc, rightDerivedFunctorPlusBaseChange_fac_app]
  simp only [← Functor.map_comp, hβ]
  simp only [Functor.map_comp, Category.assoc]
  rw [hbc, rightDerivedFunctorPlusBaseChange_fac_app_assoc]
  erw [reassoc_of% hf, reassoc_of% hγ, hK, Functor.map_comp, Category.assoc]
  rfl

end Paste

end CategoryTheory.Functor
