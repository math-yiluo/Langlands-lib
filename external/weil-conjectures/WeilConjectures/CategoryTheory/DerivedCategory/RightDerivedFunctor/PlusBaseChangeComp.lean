/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp

@[expose] public section

/-!
# Base change for bounded below right derived functors: identity and composition

The base change morphism `R⁺G ⋙ γ⁺ ⟶ β⁺ ⋙ R⁺G'` of
`CategoryTheory.Functor.rightDerivedFunctorPlusBaseChange` is compatible with the identity and
composition isomorphisms of bounded below right derived functors:

- `CategoryTheory.Functor.rightDerivedFunctorPlusBaseChange_comp`: the base change morphism of a
  pasted square is the pasting of the base change morphisms, modulo the composition isomorphisms
  `Functor.rightDerivedFunctorPlusCompIso'`;
- `CategoryTheory.Functor.rightDerivedFunctorPlusBaseChange_id`: for a square whose horizontal
  functors are identified with identity functors, the base change morphism is the composite of
  the induced identifications `R⁺G ≅ 𝟭`.

Both are proved by the uniqueness of morphisms out of a right derived functor
(`CategoryTheory.Functor.rightDerived_ext`), comparing the two sides after precomposition with
the unit.
-/

open CategoryTheory Category Limits

namespace CategoryTheory.Functor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {B C D B' C' D' : Type*} [Category* B] [Category* C] [Category* D] [Category* B']
  [Category* C'] [Category* D'] [Abelian B] [Abelian C] [Abelian D] [Abelian B'] [Abelian C']
  [Abelian D'] [HasDerivedCategory B] [HasDerivedCategory C] [HasDerivedCategory D]
  [HasDerivedCategory B'] [HasDerivedCategory C'] [HasDerivedCategory D']
  [EnoughInjectives B] [EnoughInjectives C] [EnoughInjectives B'] [EnoughInjectives C']
  {G₁ : B ⥤ C} {G₂ : C ⥤ D} {H : B ⥤ D} {G₁' : B' ⥤ C'} {G₂' : C' ⥤ D'} {H' : B' ⥤ D'}
  {β : B ⥤ B'} {γ : C ⥤ C'} {δ : D ⥤ D'}
  [G₁.Additive] [G₂.Additive] [H.Additive] [G₁'.Additive] [G₂'.Additive] [H'.Additive]
  [β.Additive] [γ.Additive] [δ.Additive]
  [PreservesFiniteLimits β] [PreservesFiniteColimits β]
  [PreservesFiniteLimits γ] [PreservesFiniteColimits γ]
  [PreservesFiniteLimits δ] [PreservesFiniteColimits δ]
  [G₁.PreservesInjectiveObjects] [G₁'.PreservesInjectiveObjects]

/-- The unit of `R⁺H` followed by the inverse of the composition isomorphism
`R⁺F ⋙ R⁺G ≅ R⁺H` is `e⁻¹` followed by the composite unit. -/
@[reassoc]
lemma rightDerivedFunctorPlusUnit_app_comp_rightDerivedFunctorPlusCompIso'_inv_app
    {C D E : Type*} [Category* C] [Category* D] [Category* E] [Abelian C] [Abelian D]
    [Abelian E] [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [EnoughInjectives C] [EnoughInjectives D] (F : C ⥤ D) (G : D ⥤ E) {H : C ⥤ E}
    [F.Additive] [G.Additive] [H.Additive] [F.PreservesInjectiveObjects] (e : F ⋙ G ≅ H)
    (M : HomotopyCategory.Plus C) :
    H.rightDerivedFunctorPlusUnith.app M ≫
        (rightDerivedFunctorPlusCompIso' F G e).inv.app (DerivedCategory.Plus.Qh.obj M) =
      DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus e.inv).app M) ≫
        (rightDerivedFunctorPlusCompUnit F G).app M := by
  have hf := congr_app (rightDerivedFunctorPlusCompIso'_fac F G e) M
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app] at hf
  rw [← cancel_mono ((rightDerivedFunctorPlusCompIso' F G e).hom.app
    (DerivedCategory.Plus.Qh.obj M)), Category.assoc, Category.assoc, hf]
  simp only [← Category.assoc, ← Functor.map_comp,
    ← NatTrans.comp_app, ← NatTrans.mapHomotopyCategoryPlus_comp, Iso.inv_hom_id,
    NatTrans.mapHomotopyCategoryPlus_id, NatTrans.id_app, Functor.map_id]
  exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- **Base change and composition.** Given squares `e₁ : G₁ ⋙ γ ⟶ β ⋙ G₁'` and
`e₂ : G₂ ⋙ δ ⟶ γ ⋙ G₂'` and a square `e : H ⋙ δ ⟶ β ⋙ H'` which is their pasting modulo
isomorphisms `G₁ ⋙ G₂ ≅ H` and `G₁' ⋙ G₂' ≅ H'`, the base change morphism of `e` is the
pasting of those of `e₁` and `e₂`, modulo the composition isomorphisms of the right derived
functors. -/
theorem rightDerivedFunctorPlusBaseChange_comp (eH : G₁ ⋙ G₂ ≅ H) (eH' : G₁' ⋙ G₂' ≅ H')
    (e₁ : G₁ ⋙ γ ⟶ β ⋙ G₁') (e₂ : G₂ ⋙ δ ⟶ γ ⋙ G₂') (e : H ⋙ δ ⟶ β ⋙ H')
    (h : ∀ X : B, δ.map (eH.inv.app X) ≫ e₂.app (G₁.obj X) ≫ G₂'.map (e₁.app X) =
      e.app X ≫ eH'.inv.app (β.obj X))
    (K : DerivedCategory.Plus B) :
    δ.mapDerivedCategoryPlus.map ((rightDerivedFunctorPlusCompIso' G₁ G₂ eH).inv.app K) ≫
        (rightDerivedFunctorPlusBaseChange e₂).app (G₁.rightDerivedFunctorPlus.obj K) ≫
        G₂'.rightDerivedFunctorPlus.map ((rightDerivedFunctorPlusBaseChange e₁).app K) =
      (rightDerivedFunctorPlusBaseChange e).app K ≫
        (rightDerivedFunctorPlusCompIso' G₁' G₂' eH').inv.app
          (β.mapDerivedCategoryPlus.obj K) := by
  let L : H.rightDerivedFunctorPlus ⋙ δ.mapDerivedCategoryPlus ⟶
      β.mapDerivedCategoryPlus ⋙ G₁'.rightDerivedFunctorPlus ⋙ G₂'.rightDerivedFunctorPlus :=
    Functor.whiskerRight (rightDerivedFunctorPlusCompIso' G₁ G₂ eH).inv
        δ.mapDerivedCategoryPlus ≫ (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft G₁.rightDerivedFunctorPlus (rightDerivedFunctorPlusBaseChange e₂) ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (rightDerivedFunctorPlusBaseChange e₁) G₂'.rightDerivedFunctorPlus ≫
      (Functor.associator _ _ _).hom
  let R : H.rightDerivedFunctorPlus ⋙ δ.mapDerivedCategoryPlus ⟶
      β.mapDerivedCategoryPlus ⋙ G₁'.rightDerivedFunctorPlus ⋙ G₂'.rightDerivedFunctorPlus :=
    rightDerivedFunctorPlusBaseChange e ≫
      Functor.whiskerLeft β.mapDerivedCategoryPlus
        (rightDerivedFunctorPlusCompIso' G₁' G₂' eH').inv
  have heq : L = R := by
    apply Functor.rightDerived_ext (H.rightDerivedFunctorPlus ⋙ δ.mapDerivedCategoryPlus)
      (Functor.whiskerRight H.rightDerivedFunctorPlusUnith δ.mapDerivedCategoryPlus ≫
        (Functor.associator _ _ _).hom) (HomotopyCategory.Plus.quasiIso B)
    apply NatTrans.ext
    funext M
    have he := congr_app (rightDerivedFunctorPlusBaseChange_fac e) M
    have he₁ := congr_app (rightDerivedFunctorPlusBaseChange_fac e₁) M
    have he₂ := congr_app (rightDerivedFunctorPlusBaseChange_fac e₂)
      (G₁.mapHomotopyCategoryPlus.obj M)
    simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
      Functor.associator_hom_app, Category.comp_id, Functor.comp_obj] at he he₁ he₂
    have hc := rightDerivedFunctorPlusUnit_app_comp_rightDerivedFunctorPlusCompIso'_inv_app
      G₁ G₂ eH M
    have hc' := rightDerivedFunctorPlusUnit_app_comp_rightDerivedFunctorPlusCompIso'_inv_app
      G₁' G₂' eH' (β.mapHomotopyCategoryPlus.obj M)
    have hn₂ := (rightDerivedFunctorPlusBaseChange e₂).naturality
      (G₁.rightDerivedFunctorPlusUnith.app M)
    simp only [Functor.comp_map, Functor.comp_obj] at hn₂
    simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Category.id_comp, Category.comp_id, Functor.comp_obj, L, R,
      Category.assoc]
    rw [reassoc_of% he, ← D+(δ).map_comp_assoc, hc, rightDerivedFunctorPlusCompUnit_app]
    simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% hn₂, reassoc_of% he₂, ← R+(G₂').map_comp, he₁]
    simp only [rightDerivedFunctorPlusBaseChangeAux, NatTrans.comp_app,
      whiskerRight_app, whiskerLeft_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Category.id_comp, Category.comp_id,
      Functor.map_comp, Category.assoc, mapHomotopyCategoryPlusCompIso_refl_hom_app,
      mapHomotopyCategoryPlusCompIso_refl_inv_app, Functor.map_id, Functor.comp_obj]
    have hRn := (rightDerivedFunctorPlusCompIso' G₁' G₂' eH').inv.naturality
      (β.mapDerivedCategoryPlusFactorsh.inv.app M)
    simp only [Functor.comp_map, Functor.comp_obj] at hRn
    rw [hRn, reassoc_of% hc', rightDerivedFunctorPlusCompUnit_app]
    have hδ := δ.mapDerivedCategoryPlusFactorsh.hom.naturality
      ((NatTrans.mapHomotopyCategoryPlus eH.inv).app M)
    simp only [Functor.comp_map, Functor.comp_obj] at hδ
    erw [reassoc_of% hδ]
    have hcancel : R+(G₂').map (γ.mapDerivedCategoryPlusFactorsh.inv.app
          (G₁.mapHomotopyCategoryPlus.obj M)) ≫
        R+(G₂').map (γ.mapDerivedCategoryPlusFactorsh.hom.app
          (G₁.mapHomotopyCategoryPlus.obj M)) = 𝟙 _ := by
      rw [← Functor.map_comp, Iso.inv_hom_id_app, Functor.map_id]
    rw [reassoc_of% hcancel]
    have hu := G₂'.rightDerivedFunctorPlusUnith.naturality
      ((NatTrans.mapHomotopyCategoryPlus e₁).app M)
    simp only [Functor.comp_map, Functor.comp_obj] at hu
    erw [← reassoc_of% hu]
    let l : H ⋙ δ ⟶ β ⋙ G₁' ⋙ G₂' :=
      Functor.whiskerRight eH.inv δ ≫ Functor.whiskerLeft G₁ e₂ ≫ Functor.whiskerRight e₁ G₂'
    let r : H ⋙ δ ⟶ β ⋙ G₁' ⋙ G₂' := e ≫ Functor.whiskerLeft β eH'.inv
    have hlr : l = r := by
      ext X
      simpa [l, r] using h X
    have hh : δ.mapHomotopyCategoryPlus.map ((NatTrans.mapHomotopyCategoryPlus eH.inv).app M) ≫
          (NatTrans.mapHomotopyCategoryPlus e₂).app (G₁.mapHomotopyCategoryPlus.obj M) ≫
          G₂'.mapHomotopyCategoryPlus.map ((NatTrans.mapHomotopyCategoryPlus e₁).app M) =
        (NatTrans.mapHomotopyCategoryPlus e).app M ≫
          (NatTrans.mapHomotopyCategoryPlus eH'.inv).app (β.mapHomotopyCategoryPlus.obj M) := by
      have ht := congr_app (congrArg NatTrans.mapHomotopyCategoryPlus hlr) M
      simp only [l, r, NatTrans.mapHomotopyCategoryPlus_comp, NatTrans.comp_app] at ht
      exact ht
    have hqh := congrArg DerivedCategory.Plus.Qh.map hh
    simp only [Functor.map_comp] at hqh
    erw [reassoc_of% hqh]
    simp only [Category.assoc]
    rfl
  simpa [L, R] using congr_app heq K

/-- The isomorphism `R⁺G ≅ 𝟭` induced by an isomorphism `G ≅ 𝟭` turns the unit of `R⁺G` into
the levelwise image of the isomorphism. -/
lemma rightDerivedFunctorPlusUnit_app_comp_natIso_trans_idIso_hom_app
    {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C] [EnoughInjectives C]
    {G : C ⥤ C} [G.Additive] (ε : G ≅ 𝟭 C) (M : HomotopyCategory.Plus C) :
    G.rightDerivedFunctorPlusUnith.app M ≫
        (rightDerivedFunctorPlusNatIso ε ≪≫ rightDerivedFunctorPlusIdIso C).hom.app
          (DerivedCategory.Plus.Qh.obj M) =
      DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus ε.hom).app M) := by
  have hn : (rightDerivedFunctorPlusNatIso ε).hom = rightDerivedFunctorPlusNatTrans ε.hom := rfl
  rw [Iso.trans_hom, NatTrans.comp_app, hn, ← Category.assoc,
    rightDerivedFunctorPlusNatTrans_app, Category.assoc, rightDerivedFunctorPlusIdIso_fac_app,
    mapHomotopyCategoryPlusIdIso_hom_app_eq_id]
  erw [DerivedCategory.Plus.Qh.map_id, Category.comp_id]

section Identity

variable {B B' : Type*} [Category* B] [Category* B'] [Abelian B] [Abelian B']
  [HasDerivedCategory B] [HasDerivedCategory B'] [EnoughInjectives B] [EnoughInjectives B']
  {G : B ⥤ B} {G' : B' ⥤ B'} {β : B ⥤ B'} [G.Additive] [G'.Additive] [β.Additive]
  [PreservesFiniteLimits β] [PreservesFiniteColimits β]

/-- The base change morphism attached to a square whose horizontal functors are identified
with identity functors is the composite of the induced identifications `R⁺G ≅ 𝟭`. -/
theorem rightDerivedFunctorPlusBaseChange_id (ε : G ≅ 𝟭 B) (ε' : G' ≅ 𝟭 B')
    (e : G ⋙ β ⟶ β ⋙ G') (h : ∀ X : B, e.app X = β.map (ε.hom.app X) ≫ ε'.inv.app (β.obj X))
    (K : DerivedCategory.Plus B) :
    (rightDerivedFunctorPlusBaseChange e).app K =
      β.mapDerivedCategoryPlus.map
          ((rightDerivedFunctorPlusNatIso ε ≪≫ rightDerivedFunctorPlusIdIso B).hom.app K) ≫
        (rightDerivedFunctorPlusNatIso ε' ≪≫ rightDerivedFunctorPlusIdIso B').inv.app
          (β.mapDerivedCategoryPlus.obj K) := by
  let ι := rightDerivedFunctorPlusNatIso ε ≪≫ rightDerivedFunctorPlusIdIso B
  let ι' := rightDerivedFunctorPlusNatIso ε' ≪≫ rightDerivedFunctorPlusIdIso B'
  let R : G.rightDerivedFunctorPlus ⋙ β.mapDerivedCategoryPlus ⟶
      β.mapDerivedCategoryPlus ⋙ G'.rightDerivedFunctorPlus :=
    Functor.whiskerRight ι.hom β.mapDerivedCategoryPlus ≫
      Functor.whiskerLeft β.mapDerivedCategoryPlus ι'.inv
  have heq : rightDerivedFunctorPlusBaseChange e = R := by
    apply Functor.rightDerived_ext (G.rightDerivedFunctorPlus ⋙ β.mapDerivedCategoryPlus)
      (Functor.whiskerRight G.rightDerivedFunctorPlusUnith β.mapDerivedCategoryPlus ≫
        (Functor.associator _ _ _).hom) (HomotopyCategory.Plus.quasiIso B)
    apply NatTrans.ext
    funext M
    have he := congr_app (rightDerivedFunctorPlusBaseChange_fac e) M
    simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
      Functor.associator_hom_app, Category.comp_id, Functor.comp_obj] at he
    simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app, Functor.associator_hom_app,
      Category.comp_id, Functor.comp_obj, R]
    rw [he, ← D+(β).map_comp_assoc]
    erw [rightDerivedFunctorPlusUnit_app_comp_natIso_trans_idIso_hom_app ε M]
    rw [← cancel_mono (ι'.hom.app (D+(β).obj (DerivedCategory.Plus.Qh.obj M))),
      Category.assoc, Iso.inv_hom_id_app]
    erw [Category.comp_id]
    simp only [rightDerivedFunctorPlusBaseChangeAux, NatTrans.comp_app,
      whiskerRight_app, whiskerLeft_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Category.id_comp, Category.comp_id,
      Category.assoc, mapHomotopyCategoryPlusCompIso_refl_hom_app,
      mapHomotopyCategoryPlusCompIso_refl_inv_app, Functor.map_id, Functor.comp_obj]
    have hn := ι'.hom.naturality (β.mapDerivedCategoryPlusFactorsh.inv.app M)
    simp only [Functor.id_map, Functor.id_obj] at hn
    erw [hn]
    erw [reassoc_of% (rightDerivedFunctorPlusUnit_app_comp_natIso_trans_idIso_hom_app ε'
      (β.mapHomotopyCategoryPlus.obj M))]
    have hδ := β.mapDerivedCategoryPlusFactorsh.hom.naturality
      ((NatTrans.mapHomotopyCategoryPlus ε.hom).app M)
    simp only [Functor.comp_map, Functor.comp_obj] at hδ
    rw [← cancel_mono (β.mapDerivedCategoryPlusFactorsh.hom.app M)]
    simp only [Category.assoc, Iso.inv_hom_id_app]
    erw [hδ]
    erw [Category.comp_id]
    have hlr : e ≫ Functor.whiskerLeft β ε'.hom = Functor.whiskerRight ε.hom β := by
      ext X
      simp [h X]
    have hh : (NatTrans.mapHomotopyCategoryPlus e).app M ≫
          (NatTrans.mapHomotopyCategoryPlus ε'.hom).app (β.mapHomotopyCategoryPlus.obj M) =
        β.mapHomotopyCategoryPlus.map ((NatTrans.mapHomotopyCategoryPlus ε.hom).app M) := by
      have ht := congr_app (congrArg NatTrans.mapHomotopyCategoryPlus hlr) M
      simp only [NatTrans.mapHomotopyCategoryPlus_comp, NatTrans.comp_app] at ht
      exact ht
    have hqh := congrArg DerivedCategory.Plus.Qh.map hh
    simp only [Functor.map_comp] at hqh
    erw [hqh]
  exact congr_app heq K

end Identity

end CategoryTheory.Functor
