/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Ambient.AmbientCompleteRawSystem
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteStagePairCategory
public import WeilConjectures.CategoryTheory.StageSystem.PbcQbarCategory
public import Mathlib.CategoryTheory.Idempotents.FunctorExtension
public import Mathlib.CategoryTheory.Idempotents.Biproducts

public import WeilConjectures.CategoryTheory.StageSystem.StageSystemFunctorDescent

import all WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarExtension
import WeilConjectures.CategoryTheory.StageSystem.CommonStageCalculus
import WeilConjectures.AlgebraicGeometry.Pbc.PbcExactCompletionData
import WeilConjectures.AlgebraicGeometry.Pbc.PbcUniformCompleteTriangulated
import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts

/-! # Ambient complete coefficient categories

Source: literature/blueprint/slopmaster2/src/version/sketch/32_smooth_base_change.tex,
lines 1191--1228, 1291--1345 and 1412--1438
(blueprint: def-sbc-ambient-complete-coefficient-categories).

This file records the ambient and constructible finite-stage categories, their
Karoubi completions, and the common-stage pair categories. The tensor transitions
are fixed by integral tensor and raw localization. Both
finite-stage and outer idempotents are retained in the common-stage categories.

## Main definitions

* `pbcAmbientCompleteSystem` and `pbcConstructibleCompleteSystem`: canonical tensors.
* `pbcAmbientCompleteQbarCategory` and `pbcConstructibleCompleteQbarCategory`:
  the two nested Karoubi categories.
* `pbcConstructibleCompleteQbarInclusion`: the canonical descended inclusion.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048

universe u v

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace CategoryTheory

private theorem coefficientSquare_unit
    {C D : Type*} [Category* C] [Category* D]
    (J : C ⥤ D) (U : D ⥤ D) (T : C ⥤ C)
    (hU : U = 𝟭 _) (hT : T = 𝟭 _) : J ⋙ U = T ⋙ J := by
  subst U
  subst T
  rfl

private theorem coefficientIso_transport_tower
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category* C₀] [Category* C₁] [Category* C₂]
    [Category* D₀] [Category* D₁] [Category* D₂]
    (T₀ : C₀ ⥤ C₁) (T₁ : C₁ ⥤ C₂) (T₂ : C₀ ⥤ C₂)
    (U₀ : D₀ ⥤ D₁) (U₁ : D₁ ⥤ D₂) (U₂ : D₀ ⥤ D₂)
    (J₀ : C₀ ⥤ D₀) (J₁ : C₁ ⥤ D₁) (J₂ : C₂ ⥤ D₂)
    (aT : T₀ ⋙ T₁ ≅ T₂) (aU : U₀ ⋙ U₁ ≅ U₂)
    (e₀ : J₀ ⋙ U₀ = T₀ ⋙ J₁) (e₁ : J₁ ⋙ U₁ = T₁ ⋙ J₂)
    (e₂ : J₀ ⋙ U₂ = T₂ ⋙ J₂)
    (h : ∀ X, HEq (J₂.map (aT.hom.app X)) (aU.hom.app (J₀.obj X)))
    (X : C₀) :
    U₁.map ((eqToIso e₀).hom.app X) ≫
      (eqToIso e₁).hom.app (T₀.obj X) ≫ J₂.map (aT.hom.app X) =
      aU.hom.app (J₀.obj X) ≫ (eqToIso e₂).hom.app X := by
  simp only [eqToIso.hom, eqToHom_app, eqToHom_map, eqToHom_trans_assoc]
  apply eq_of_heq
  exact (eqToHom_comp_heq _ _).trans
    ((h X).trans (comp_eqToHom_heq _ _).symm)

private theorem coefficientIso_transport_iff
    {C D : Type*} [Category* C] [Category* D] {F G : C ⥤ D}
    (e : F = G) (b : F ≅ G)
    (hb : ∀ X, HEq (b.hom.app X) (𝟙 (F.obj X))) : b = eqToIso e := by
  apply Iso.ext
  ext X
  simpa only [eqToIso.hom, eqToHom_app] using eq_of_heq ((hb X).trans
    (eqToHom_heq_id_dom _ _ (Functor.congr_obj e X)).symm)

private theorem coefficientIso_identity_exists
    {C D : Type*} [Category* C] [Category* D] {F G : C ⥤ D} (e : F = G) :
    ∃! b : F ≅ G, ∀ X, HEq (b.hom.app X) (𝟙 (F.obj X)) := by
  let b := eqToIso e
  have hb : ∀ X, HEq (b.hom.app X) (𝟙 (F.obj X)) := by
    intro X
    simpa only [b, eqToIso.hom, eqToHom_app] using
      eqToHom_heq_id_dom _ _ (Functor.congr_obj e X)
  refine ⟨b, hb, fun c hc ↦ ?_⟩
  apply Iso.ext
  ext X
  exact eq_of_heq ((hc X).trans (hb X).symm)

private theorem coefficientIso_identity_tower
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category* C₀] [Category* C₁] [Category* C₂]
    [Category* D₀] [Category* D₁] [Category* D₂]
    (T₀ : C₀ ⥤ C₁) (T₁ : C₁ ⥤ C₂) (T₂ : C₀ ⥤ C₂)
    (U₀ : D₀ ⥤ D₁) (U₁ : D₁ ⥤ D₂) (U₂ : D₀ ⥤ D₂)
    (J₀ : C₀ ⥤ D₀) (J₁ : C₁ ⥤ D₁) (J₂ : C₂ ⥤ D₂)
    (aT : T₀ ⋙ T₁ ≅ T₂) (aU : U₀ ⋙ U₁ ≅ U₂)
    (e₀ : J₀ ⋙ U₀ = T₀ ⋙ J₁) (e₁ : J₁ ⋙ U₁ = T₁ ⋙ J₂)
    (e₂ : J₀ ⋙ U₂ = T₂ ⋙ J₂)
    (b₀ : J₀ ⋙ U₀ ≅ T₀ ⋙ J₁) (b₁ : J₁ ⋙ U₁ ≅ T₁ ⋙ J₂)
    (b₂ : J₀ ⋙ U₂ ≅ T₂ ⋙ J₂)
    (hb₀ : ∀ X, HEq (b₀.hom.app X) (𝟙 ((J₀ ⋙ U₀).obj X)))
    (hb₁ : ∀ X, HEq (b₁.hom.app X) (𝟙 ((J₁ ⋙ U₁).obj X)))
    (hb₂ : ∀ X, HEq (b₂.hom.app X) (𝟙 ((J₀ ⋙ U₂).obj X)))
    (h : ∀ X, HEq (J₂.map (aT.hom.app X)) (aU.hom.app (J₀.obj X))) (X : C₀) :
    U₁.map (b₀.hom.app X) ≫ b₁.hom.app (T₀.obj X) ≫ J₂.map (aT.hom.app X) =
      aU.hom.app (J₀.obj X) ≫ b₂.hom.app X := by
  have h₀ := coefficientIso_transport_iff e₀ b₀ hb₀
  have h₁ := coefficientIso_transport_iff e₁ b₁ hb₁
  have h₂ := coefficientIso_transport_iff e₂ b₂ hb₂
  subst b₀
  subst b₁
  subst b₂
  exact coefficientIso_transport_tower T₀ T₁ T₂ U₀ U₁ U₂ J₀ J₁ J₂ aT aU e₀ e₁ e₂ h X

private theorem coefficientIso_hom_app_id
    {C D : Type*} [Category* C] [Category* D]
    {F G F' G' : C ⥤ D} (hF : F = F') (hG : G = G')
    (b : F ≅ G) (e : F' = G') (h : HEq b (eqToIso e)) (X : C) :
    HEq (b.hom.app X) (𝟙 (F.obj X)) := by
  subst F'
  subst G'
  have hb := eq_of_heq h
  subst b
  simpa only [eqToIso.hom, eqToHom_app] using
    eqToHom_heq_id_dom _ _ (Functor.congr_obj e X)

private theorem coefficientLocalizedAssociator_heq
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category* C₀] [Category* C₁] [Category* C₂]
    [Category* D₀] [Category* D₁] [Category* D₂]
    (Q₀ : C₀ ⥤ D₀) (Q₁ : C₁ ⥤ D₁) (Q₂ : C₂ ⥤ D₂)
    (T₀ : C₀ ⥤ C₁) (T₁ : C₁ ⥤ C₂) (T₂ : C₀ ⥤ C₂)
    (U₀ : D₀ ⥤ D₁) (U₁ : D₁ ⥤ D₂) (U₂ : D₀ ⥤ D₂)
    (e₀ : Q₀ ⋙ U₀ = T₀ ⋙ Q₁) (e₁ : Q₁ ⋙ U₁ = T₁ ⋙ Q₂)
    (e₂ : Q₀ ⋙ U₂ = T₂ ⋙ Q₂)
    (c₀ : Q₀ ⋙ U₀ ≅ T₀ ⋙ Q₁) (c₁ : Q₁ ⋙ U₁ ≅ T₁ ⋙ Q₂)
    (c₂ : Q₀ ⋙ U₂ ≅ T₂ ⋙ Q₂)
    (hc₀ : ∀ X, HEq (c₀.hom.app X) (𝟙 ((Q₀ ⋙ U₀).obj X)))
    (hc₁ : ∀ X, HEq (c₁.hom.app X) (𝟙 ((Q₁ ⋙ U₁).obj X)))
    (hc₂ : ∀ X, HEq (c₂.hom.app X) (𝟙 ((Q₀ ⋙ U₂).obj X)))
    (a : T₀ ⋙ T₁ ≅ T₂) (b : U₀ ⋙ U₁ ≅ U₂)
    (hb : ∀ X, b.hom.app (Q₀.obj X) = U₁.map (c₀.hom.app X) ≫
      c₁.hom.app (T₀.obj X) ≫ Q₂.map (a.hom.app X) ≫ c₂.inv.app X) (X : C₀) :
    HEq (b.hom.app (Q₀.obj X)) (Q₂.map (a.hom.app X)) := by
  have h₀ : c₀ = eqToIso e₀ := coefficientIso_transport_iff e₀ c₀ hc₀
  have h₁ : c₁ = eqToIso e₁ := coefficientIso_transport_iff e₁ c₁ hc₁
  have h₂ : c₂ = eqToIso e₂ := coefficientIso_transport_iff e₂ c₂ hc₂
  rw [hb X, h₀, h₁, h₂]
  simp only [eqToIso.hom, eqToIso.inv, eqToHom_app, eqToHom_map,
    eqToHom_trans_assoc]
  exact (eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)

private theorem coefficientTower_leftUnit
    {C D D' C' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    (S₀ : C ⥤ C) (T₀ : D ⥤ D) (S₁ : C ⥤ C') (T₁ : D ⥤ D')
    (J₀ : C ⥤ D) (J₁ : C' ⥤ D')
    (aS : S₀ ⋙ S₁ ≅ S₁) (aT : T₀ ⋙ T₁ ≅ T₁)
    (b₀ : J₀ ⋙ T₀ ≅ S₀ ⋙ J₀) (b₁ : J₀ ⋙ T₁ ≅ S₁ ⋙ J₁)
    (hS : S₀ = 𝟭 _) (hT : T₀ = 𝟭 _)
    (haS : HEq aS S₁.leftUnitor) (haT : HEq aT T₁.leftUnitor)
    (hb : ∀ X, HEq (b₀.hom.app X) (𝟙 ((J₀ ⋙ T₀).obj X))) (X : C) :
    T₁.map (b₀.hom.app X) ≫ b₁.hom.app (S₀.obj X) ≫ J₁.map (aS.hom.app X) =
      aT.hom.app (J₀.obj X) ≫ b₁.hom.app X := by
  subst S₀
  subst T₀
  have hs : aS = S₁.leftUnitor := eq_of_heq haS
  have ht : aT = T₁.leftUnitor := eq_of_heq haT
  subst aS
  subst aT
  have hb' := eq_of_heq (hb X)
  change T₁.map (b₀.hom.app X) ≫ b₁.hom.app X ≫ J₁.map (𝟙 _) =
    𝟙 _ ≫ b₁.hom.app X
  rw [hb']
  simp only [Functor.map_id, Category.id_comp]
  exact Category.comp_id _

private theorem coefficientTower_rightUnit
    {C D D' C' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    (S₁ : C' ⥤ C') (T₁ : D' ⥤ D') (S₀ : C ⥤ C') (T₀ : D ⥤ D')
    (J₀ : C ⥤ D) (J₁ : C' ⥤ D')
    (aS : S₀ ⋙ S₁ ≅ S₀) (aT : T₀ ⋙ T₁ ≅ T₀)
    (b₁ : J₁ ⋙ T₁ ≅ S₁ ⋙ J₁) (b₀ : J₀ ⋙ T₀ ≅ S₀ ⋙ J₁)
    (hS : S₁ = 𝟭 _) (hT : T₁ = 𝟭 _)
    (haS : HEq aS S₀.rightUnitor) (haT : HEq aT T₀.rightUnitor)
    (hb : ∀ X, HEq (b₁.hom.app X) (𝟙 ((J₁ ⋙ T₁).obj X))) (X : C) :
    T₁.map (b₀.hom.app X) ≫ b₁.hom.app (S₀.obj X) ≫ J₁.map (aS.hom.app X) =
      aT.hom.app (J₀.obj X) ≫ b₀.hom.app X := by
  subst S₁
  subst T₁
  have hs : aS = S₀.rightUnitor := eq_of_heq haS
  have ht : aT = T₀.rightUnitor := eq_of_heq haT
  subst aS
  subst aT
  have hb' := eq_of_heq (hb (S₀.obj X))
  change b₀.hom.app X ≫ b₁.hom.app (S₀.obj X) ≫ J₁.map (𝟙 _) =
    𝟙 _ ≫ b₀.hom.app X
  rw [hb']
  simp only [Functor.map_id, Category.id_comp]
  change b₀.hom.app X ≫ 𝟙 _ ≫ 𝟙 _ = b₀.hom.app X
  simp only [Category.comp_id]

private theorem coefficientFunctor_map_heq
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {X Y X' Y' : C} (hX : X = X') (hY : Y = Y')
    (f : X ⟶ Y) (g : X' ⟶ Y') (h : HEq f g) : HEq (F.map f) (F.map g) := by
  subst X'
  subst Y'
  cases h
  rfl

private theorem coefficientFactorization_comp_obj
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category* C₀] [Category* C₁] [Category* C₂]
    [Category* D₀] [Category* D₁] [Category* D₂]
    (Q₀ : C₀ ⥤ D₀) (Q₁ : C₁ ⥤ D₁) (Q₂ : C₂ ⥤ D₂)
    (T₀ : C₀ ⥤ C₁) (T₁ : C₁ ⥤ C₂)
    (U₀ : D₀ ⥤ D₁) (U₁ : D₁ ⥤ D₂)
    (h₀ : Q₀ ⋙ U₀ = T₀ ⋙ Q₁) (h₁ : Q₁ ⋙ U₁ = T₁ ⋙ Q₂) (X : C₀) :
    (U₀ ⋙ U₁).obj (Q₀.obj X) = Q₂.obj ((T₀ ⋙ T₁).obj X) :=
  (congrArg U₁.obj (Functor.congr_obj h₀ X)).trans
    (Functor.congr_obj h₁ (T₀.obj X))

private theorem coefficientFullSubcategory_hom_heq
    {C : Type*} [Category* C] (P : ObjectProperty C)
    {X Y X' Y' : P.FullSubcategory} (hx : X = X') (hy : Y = Y')
    (f : X ⟶ Y) (g : X' ⟶ Y') (h : HEq f.hom g.hom) : HEq f g := by
  subst X'
  subst Y'
  apply heq_of_eq
  apply ObjectProperty.hom_ext
  exact eq_of_heq h

private theorem coefficientNatTrans_app_obj_heq
    {C D : Type*} [Category* C] [Category* D] {F G : C ⥤ D}
    (α : F ⟶ G) {X Y : C} (h : X = Y) : HEq (α.app X) (α.app Y) := by
  subst Y
  rfl

private theorem coefficientNatTrans_app_heq
    {C D : Type*} [Category* C] [Category* D]
    {F G F' G' : C ⥤ D} (hF : F = F') (hG : G = G')
    (α : F ⟶ G) (β : F' ⟶ G') (h : HEq α β) (X : C) :
    HEq (α.app X) (β.app X) := by
  subst F'
  subst G'
  cases h
  rfl

private theorem coefficientLocalizedInclusion_associator
    {C₀ C₁ D₀ D₁ A₀ A₁ B₀ B₁ : Type*}
    [Category* C₀] [Category* C₁] [Category* D₀] [Category* D₁]
    [Category* A₀] [Category* A₁] [Category* B₀] [Category* B₁]
    (QC₀ : C₀ ⥤ D₀) (QC₁ : C₁ ⥤ D₁) (QA₀ : A₀ ⥤ B₀) (QA₁ : A₁ ⥤ B₁)
    (JI₀ : C₀ ⥤ A₀) (JI₁ : C₁ ⥤ A₁) (JR₀ : D₀ ⥤ B₀) (JR₁ : D₁ ⥤ B₁)
    (FI GI : C₀ ⥤ C₁) (FA GA : A₀ ⥤ A₁)
    (FR GR : D₀ ⥤ D₁) (FS GS : B₀ ⥤ B₁)
    (aI : FI ≅ GI) (aA : FA ≅ GA) (aR : FR ≅ GR) (aS : FS ≅ GS)
    (hj₀ : QC₀ ⋙ JR₀ = JI₀ ⋙ QA₀) (hj₁ : QC₁ ⋙ JR₁ = JI₁ ⋙ QA₁)
    (hcX : ∀ K, FR.obj (QC₀.obj K) = QC₁.obj (FI.obj K))
    (hcY : ∀ K, GR.obj (QC₀.obj K) = QC₁.obj (GI.obj K))
    (hiX : ∀ K, JI₁.obj (FI.obj K) = FA.obj (JI₀.obj K))
    (hiY : ∀ K, JI₁.obj (GI.obj K) = GA.obj (JI₀.obj K))
    (hc : ∀ K, HEq (aR.hom.app (QC₀.obj K)) (QC₁.map (aI.hom.app K)))
    (ha : ∀ K, HEq (aS.hom.app (QA₀.obj K)) (QA₁.map (aA.hom.app K)))
    (hi : ∀ K, HEq (JI₁.map (aI.hom.app K)) (aA.hom.app (JI₀.obj K)))
    (hQ : ∀ X, ∃ K, QC₀.obj K = X) (X : D₀) :
    HEq (JR₁.map (aR.hom.app X)) (aS.hom.app (JR₀.obj X)) := by
  obtain ⟨K, rfl⟩ := hQ X
  have h₁ := coefficientFunctor_map_heq JR₁ (hcX K) (hcY K)
    (aR.hom.app (QC₀.obj K)) (QC₁.map (aI.hom.app K)) (hc K)
  have h₂ := Functor.hcongr_hom hj₁ (aI.hom.app K)
  have h₃ := coefficientFunctor_map_heq QA₁ (hiX K) (hiY K)
    (JI₁.map (aI.hom.app K)) (aA.hom.app (JI₀.obj K)) (hi K)
  have h₄ := coefficientNatTrans_app_obj_heq aS.hom (Functor.congr_obj hj₀ K).symm
  exact h₁.trans (h₂.trans (h₃.trans ((ha (JI₀.obj K)).symm.trans h₄)))

private theorem coefficientSystem_identityTower
    {I : Type*} [Preorder I] {A B : I → Type*}
    [∀ i, Category* (A i)] [∀ i, Category* (B i)]
    (S : StageSystem A) (T : StageSystem B) (J : ∀ i, A i ⥤ B i)
    (e : ∀ {i j} (h : i ≤ j), J i ⋙ T.T h = S.T h ⋙ J j)
    (b : ∀ {i j} (h : i ≤ j), J i ⋙ T.T h ≅ S.T h ⋙ J j)
    (hb : ∀ {i j} (h : i ≤ j) (X : A i),
      HEq ((b h).hom.app X) (𝟙 ((J i ⋙ T.T h).obj X)))
    {i j k : I} (h : i ≤ j) (h' : j ≤ k)
    (ha : ∀ X, HEq ((J k).map ((S.assoc h h').hom.app X))
      ((T.assoc h h').hom.app ((J i).obj X))) (X : A i) :
    (T.T h').map ((b h).hom.app X) ≫ (b h').hom.app ((S.T h).obj X) ≫
      (J k).map ((S.assoc h h').hom.app X) =
      (T.assoc h h').hom.app ((J i).obj X) ≫ (b (h.trans h')).hom.app X :=
  coefficientIso_identity_tower (S.T h) (S.T h') (S.T (h.trans h'))
    (T.T h) (T.T h') (T.T (h.trans h')) (J i) (J j) (J k)
    (S.assoc h h') (T.assoc h h') (e h) (e h') (e (h.trans h'))
    (b h) (b h') (b (h.trans h')) (hb h) (hb h') (hb (h.trans h')) ha X

private theorem coefficientSystem_identityTower_of_units
    {I : Type*} [Preorder I] {A B : I → Type*}
    [∀ i, Category* (A i)] [∀ i, Category* (B i)]
    (S : StageSystem A) (T : StageSystem B) (J : ∀ i, A i ⥤ B i)
    (e : ∀ {i j} (h : i ≤ j), J i ⋙ T.T h = S.T h ⋙ J j)
    (b : ∀ {i j} (h : i ≤ j), J i ⋙ T.T h ≅ S.T h ⋙ J j)
    (hb : ∀ {i j} (h : i ≤ j) (X : A i),
      HEq ((b h).hom.app X) (𝟙 ((J i ⋙ T.T h).obj X)))
    (hS : ∀ i, S.T (le_refl i) = 𝟭 _) (hT : ∀ i, T.T (le_refl i) = 𝟭 _)
    (hSL : ∀ {i j} (h : i ≤ j),
      HEq (S.assoc (le_refl i) h) (Functor.leftUnitor (S.T h)))
    (hSR : ∀ {i j} (h : i ≤ j),
      HEq (S.assoc h (le_refl j)) (Functor.rightUnitor (S.T h)))
    (hTL : ∀ {i j} (h : i ≤ j),
      HEq (T.assoc (le_refl i) h) (Functor.leftUnitor (T.T h)))
    (hTR : ∀ {i j} (h : i ≤ j),
      HEq (T.assoc h (le_refl j)) (Functor.rightUnitor (T.T h)))
    (ha : ∀ {i j k} (h : i ≤ j) (h' : j ≤ k), i ≠ j → j ≠ k → ∀ X,
      HEq ((J k).map ((S.assoc h h').hom.app X))
        ((T.assoc h h').hom.app ((J i).obj X)))
    {i j k : I} (h : i ≤ j) (h' : j ≤ k) (X : A i) :
    (T.T h').map ((b h).hom.app X) ≫ (b h').hom.app ((S.T h).obj X) ≫
      (J k).map ((S.assoc h h').hom.app X) =
      (T.assoc h h').hom.app ((J i).obj X) ≫ (b (h.trans h')).hom.app X := by
  classical
  by_cases hij : i = j
  · subst j
    exact coefficientTower_leftUnit (S.T (le_refl i)) (T.T (le_refl i))
      (S.T h') (T.T h') (J i) (J k) (S.assoc (le_refl i) h')
      (T.assoc (le_refl i) h') (b (le_refl i)) (b h')
      (hS i) (hT i) (hSL h') (hTL h') (hb (le_refl i)) X
  by_cases hjk : j = k
  · subst k
    exact coefficientTower_rightUnit (S.T (le_refl j)) (T.T (le_refl j))
      (S.T h) (T.T h) (J i) (J j) (S.assoc h (le_refl j))
      (T.assoc h (le_refl j)) (b (le_refl j)) (b h)
      (hS j) (hT j) (hSR h) (hTR h) (hb (le_refl j)) X
  exact coefficientSystem_identityTower S T J e b hb h h' (ha h h' hij hjk) X

end CategoryTheory

namespace CategoryTheory.Localization

private theorem coefficientLiftIso_id
    {C D H : Type*} [Category* C] [Category* D] [Category* H]
    (Q : C ⥤ D) (P : MorphismProperty C) [Q.IsLocalization P]
    (L R : D ⥤ H) (e : Q ⋙ L = Q ⋙ R) (X : C) :
    HEq ((liftNatIso Q P (Q ⋙ L) (Q ⋙ R) L R (eqToIso e)).hom.app (Q.obj X))
      (𝟙 (L.obj (Q.obj X))) := by
  change HEq ((liftNatTrans Q P (Q ⋙ L) (Q ⋙ R) L R
    (eqToIso e).hom).app (Q.obj X)) _
  rw [liftNatTrans_app]
  simp only [Lifting.iso, Iso.refl_hom,
    Iso.refl_inv, NatTrans.id_app, Category.id_comp, Category.comp_id,
    eqToIso.hom, eqToHom_app]
  exact eqToHom_heq_id_dom _ _ _

end CategoryTheory.Localization

namespace CategoryTheory.Localization

private theorem coefficientFunctor_eq
    {C D H : Type*} [Category* C] [Category* D] [Category* H]
    (Q : C ⥤ D) (P : MorphismProperty C) [Q.IsLocalization P]
    (hQ : Function.Surjective Q.obj) (L R : D ⥤ H) (e : Q ⋙ L = Q ⋙ R) : L = R := by
  have ho (Y : D) : L.obj Y = R.obj Y := by
    obtain ⟨X, rfl⟩ := hQ Y
    exact Functor.congr_obj e X
  refine Functor.ext_of_iso (liftNatIso Q P (Q ⋙ L) (Q ⋙ R) L R (eqToIso e)) ho ?_
  intro Y
  obtain ⟨X, rfl⟩ := hQ Y
  exact eq_of_heq ((coefficientLiftIso_id Q P L R e X).trans
    (eqToHom_heq_id_dom _ _ (ho (Q.obj X))).symm)

end CategoryTheory.Localization

namespace CategoryTheory.Localization

private theorem coefficientSquare_eq
    {C₀ C₁ D₀ D₁ R₀ R₁ S₀ S₁ : Type*}
    [Category* C₀] [Category* C₁] [Category* D₀] [Category* D₁]
    [Category* R₀] [Category* R₁] [Category* S₀] [Category* S₁]
    (QC₀ : C₀ ⥤ R₀) (QC₁ : C₁ ⥤ R₁) (QD₀ : D₀ ⥤ S₀) (QD₁ : D₁ ⥤ S₁)
    (J₀ : C₀ ⥤ D₀) (J₁ : C₁ ⥤ D₁) (T : C₀ ⥤ C₁) (U : D₀ ⥤ D₁)
    (j₀ : R₀ ⥤ S₀) (j₁ : R₁ ⥤ S₁) (t : R₀ ⥤ R₁) (u : S₀ ⥤ S₁)
    (hj₀ : QC₀ ⋙ j₀ = J₀ ⋙ QD₀) (hj₁ : QC₁ ⋙ j₁ = J₁ ⋙ QD₁)
    (ht : QC₀ ⋙ t = T ⋙ QC₁) (hu : QD₀ ⋙ u = U ⋙ QD₁)
    (hJ : J₀ ⋙ U = T ⋙ J₁) (P : MorphismProperty C₀) [QC₀.IsLocalization P]
    (hQ : ∀ X : R₀, ∃ Y, QC₀.obj Y = X) :
    j₀ ⋙ u = t ⋙ j₁ := by
  have he : QC₀ ⋙ (j₀ ⋙ u) = QC₀ ⋙ (t ⋙ j₁) := by
    calc
      _ = (J₀ ⋙ QD₀) ⋙ u := congrArg (· ⋙ u) hj₀
      _ = J₀ ⋙ (U ⋙ QD₁) := congrArg (J₀ ⋙ ·) hu
      _ = (T ⋙ J₁) ⋙ QD₁ := congrArg (· ⋙ QD₁) hJ
      _ = T ⋙ (QC₁ ⋙ j₁) := congrArg (T ⋙ ·) hj₁.symm
      _ = _ := congrArg (· ⋙ j₁) ht.symm
  exact coefficientFunctor_eq QC₀ P hQ (j₀ ⋙ u) (t ⋙ j₁) he

end CategoryTheory.Localization

namespace CategoryTheory.ScalarLocalization

private theorem coefficientBetween_localization
    (R : Type*) [CommRing R] (p : R)
    {C D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D] [Linear R C] [Linear R D]
    (F : C ⥤ D) [F.Additive] [F.Linear R] :
    localization R C p ⋙ between R p F = F ⋙ localization R D p := by
  apply Functor.hext (fun _ ↦ rfl)
  intro X Y f
  apply heq_of_eq
  simp [between, betweenHom, localization]

end CategoryTheory.ScalarLocalization

namespace CategoryTheory.Idempotents

universe a b c x y z
variable {C : Type a} [Category.{x} C] {D : Type b} [Category.{y} D]
  {H : Type c} [Category.{z} H]

/-- Extend an inclusion comparison with its composed functor types fixed abstractly.
This is Mathlib's projector-sandwiched extension, with the same object and arrow formulas.
Source: sketch32, lines 1291--1311 and 1419--1426
(blueprint: def-sbc-ambient-complete-coefficient-categories). -/
@[irreducible] def coefficientInclusionComparisonIso
    {C₀ C₁ D₀ D₁ : Type*} [Category* C₀] [Category* C₁]
    [Category* D₀] [Category* D₁]
    (J₀ : C₀ ⥤ D₀) (U : D₀ ⥤ D₁) (V : C₀ ⥤ C₁) (J₁ : C₁ ⥤ D₁)
    (b : J₀ ⋙ U ≅ V ⋙ J₁) :
    (functorExtension₂ _ _).obj J₀ ⋙ (functorExtension₂ _ _).obj U ≅
      (functorExtension₂ _ _).obj V ⋙ (functorExtension₂ _ _).obj J₁ :=
  (functorExtension₂ _ _).mapIso b

/-- Extend a tensor associator with its composed functor types fixed abstractly.
The construction retains the given object, projector, and arrow formulas.
Source: sketch32, lines 1291--1338
(blueprint: def-sbc-ambient-complete-coefficient-categories). -/
@[irreducible] def coefficientAssociatorIso (F : C ⥤ D) (G : D ⥤ H) (L : C ⥤ H)
    (a : F ⋙ G ≅ L) :
    (functorExtension₂ _ _).obj F ⋙ (functorExtension₂ _ _).obj G ≅
      (functorExtension₂ _ _).obj L := (functorExtension₂ _ _).mapIso a

end CategoryTheory.Idempotents

namespace CategoryTheory.Idempotents

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe a b c x y z
variable {C : Type a} [Category.{x} C] {D : Type b} [Category.{y} D]
  {H : Type c} [Category.{z} H]

/-- Karoubi extension preserves a coherent tensor-associator equation.
Source: sketch32, lines 1291--1338; the naturality and idempotence computation
(blueprint: def-sbc-ambient-complete-coefficient-categories). -/
private theorem coefficientExtension_cocycle
    {A₀ A₁ A₂ A₃ : Type*} [Category* A₀] [Category* A₁] [Category* A₂] [Category* A₃]
    (F₀₁ : A₀ ⥤ A₁) (F₁₂ : A₁ ⥤ A₂) (F₂₃ : A₂ ⥤ A₃)
    (F₀₂ : A₀ ⥤ A₂) (F₁₃ : A₁ ⥤ A₃) (F₀₃ : A₀ ⥤ A₃)
    (a₀₁₂ : F₀₁ ⋙ F₁₂ ≅ F₀₂) (a₁₂₃ : F₁₂ ⋙ F₂₃ ≅ F₁₃)
    (a₀₂₃ : F₀₂ ⋙ F₂₃ ≅ F₀₃) (a₀₁₃ : F₀₁ ⋙ F₁₃ ≅ F₀₃)
    (h : ∀ X, F₂₃.map (a₀₁₂.hom.app X) ≫ a₀₂₃.hom.app X =
      a₁₂₃.hom.app (F₀₁.obj X) ≫ a₀₁₃.hom.app X) (P : Karoubi A₀) :
    ((functorExtension₂ _ _).obj F₂₃).map
        ((coefficientAssociatorIso F₀₁ F₁₂ F₀₂ a₀₁₂).hom.app P) ≫
      (coefficientAssociatorIso F₀₂ F₂₃ F₀₃ a₀₂₃).hom.app P =
    (coefficientAssociatorIso F₁₂ F₂₃ F₁₃ a₁₂₃).hom.app
          (((functorExtension₂ _ _).obj F₀₁).obj P) ≫
      (coefficientAssociatorIso F₀₁ F₁₃ F₀₃ a₀₁₃).hom.app P := by
  unfold coefficientAssociatorIso
  apply Karoubi.hom_ext
  simp only [Karoubi.comp_f, functorExtension₂_obj_map_f,
    Functor.mapIso_hom, functorExtension₂_map_app_f,
    functorExtension₂_obj_obj_p,
    Functor.map_comp, Category.assoc]
  simp only [← Functor.comp_map]
  simp only [a₀₂₃.hom.naturality_assoc, a₀₁₃.hom.naturality_assoc]
  simp only [← Category.assoc, ← Functor.map_comp, P.idem]
  change (F₂₃.map (a₀₁₂.hom.app P.X) ≫ a₀₂₃.hom.app P.X) ≫ F₀₃.map P.p =
    (a₁₂₃.hom.app (F₀₁.obj P.X) ≫ a₀₁₃.hom.app P.X) ≫ F₀₃.map P.p
  exact congrArg (· ≫ F₀₃.map P.p) (h P.X)

private theorem coefficientExtension_whiskerRight
    {F G : C ⥤ D} (α : F ⟶ G) (L : D ⥤ H) :
    (functorExtension₂ _ _).map (Functor.whiskerRight α L) =
      Functor.whiskerRight ((functorExtension₂ _ _).map α)
        ((functorExtension₂ _ _).obj L) := by
  ext P
  change L.map (F.map P.p) ≫ L.map (α.app P.X) = L.map (F.map P.p ≫ α.app P.X)
  exact (L.map_comp _ _).symm

private theorem coefficientExtension_whiskerLeft
    (F : C ⥤ D) {G L : D ⥤ H} (α : G ⟶ L) :
    (functorExtension₂ _ _).map (Functor.whiskerLeft F α) =
      Functor.whiskerLeft ((functorExtension₂ _ _).obj F)
        ((functorExtension₂ _ _).map α) := by
  rfl

private theorem coefficientExtension_inclusionTower
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category* C₀] [Category* C₁] [Category* C₂]
    [Category* D₀] [Category* D₁] [Category* D₂]
    (T₀ : C₀ ⥤ C₁) (T₁ : C₁ ⥤ C₂) (T₂ : C₀ ⥤ C₂)
    (U₀ : D₀ ⥤ D₁) (U₁ : D₁ ⥤ D₂) (U₂ : D₀ ⥤ D₂)
    (J₀ : C₀ ⥤ D₀) (J₁ : C₁ ⥤ D₁) (J₂ : C₂ ⥤ D₂)
    (aT : T₀ ⋙ T₁ ≅ T₂) (aU : U₀ ⋙ U₁ ≅ U₂)
    (b₀ : J₀ ⋙ U₀ ≅ T₀ ⋙ J₁) (b₁ : J₁ ⋙ U₁ ≅ T₁ ⋙ J₂)
    (b₂ : J₀ ⋙ U₂ ≅ T₂ ⋙ J₂)
    (h : ∀ X, U₁.map (b₀.hom.app X) ≫ b₁.hom.app (T₀.obj X) ≫
      J₂.map (aT.hom.app X) = aU.hom.app (J₀.obj X) ≫ b₂.hom.app X)
    (P : Karoubi C₀) :
    ((functorExtension₂ _ _).obj U₁).map
        ((coefficientInclusionComparisonIso J₀ U₀ T₀ J₁ b₀).hom.app P) ≫
      (coefficientInclusionComparisonIso J₁ U₁ T₁ J₂ b₁).hom.app
        (((functorExtension₂ _ _).obj T₀).obj P) ≫
      ((functorExtension₂ _ _).obj J₂).map
        ((coefficientAssociatorIso T₀ T₁ T₂ aT).hom.app P) =
    (coefficientAssociatorIso U₀ U₁ U₂ aU).hom.app
        (((functorExtension₂ _ _).obj J₀).obj P) ≫
      (coefficientInclusionComparisonIso J₀ U₂ T₂ J₂ b₂).hom.app P := by
  unfold coefficientAssociatorIso
  unfold coefficientInclusionComparisonIso
  have hn : Functor.whiskerRight b₀.hom U₁ ≫ Functor.whiskerLeft T₀ b₁.hom ≫
      Functor.whiskerRight aT.hom J₂ = Functor.whiskerLeft J₀ aU.hom ≫ b₂.hom := by
    ext X
    exact h X
  have he := congrArg ((functorExtension₂ _ _).map) hn
  simp only [Functor.map_comp, coefficientExtension_whiskerRight,
    coefficientExtension_whiskerLeft] at he
  have hp := congrArg (fun α ↦ α.app P) he
  simpa only [Functor.mapIso_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, NatTrans.comp_app] using hp

private theorem coefficientExtension_inclusionUnit (J : C ⥤ D)
    (U : D ⥤ D) (V : C ⥤ C) (b : J ⋙ U ≅ V ⋙ J)
    (hU : U = 𝟭 _) (hV : V = 𝟭 _)
    (hb : ∀ X, HEq (b.hom.app X) (𝟙 ((J ⋙ U).obj X))) :
    HEq (coefficientInclusionComparisonIso J U V J b)
      (((functorExtension₂ _ _).obj J).rightUnitor ≪≫
        ((functorExtension₂ _ _).obj J).leftUnitor.symm) := by
  unfold coefficientInclusionComparisonIso
  subst U
  subst V
  have eb : b = J.rightUnitor ≪≫ J.leftUnitor.symm := by
    apply Iso.ext
    ext X
    simpa using eq_of_heq (hb X)
  subst b
  apply heq_of_eq
  apply Iso.ext
  ext P
  change J.map P.p ≫ (𝟙 _ ≫ 𝟙 _) = J.map P.p ≫ J.map P.p
  simp only [Category.comp_id, ← J.map_comp, P.idem]

private theorem coefficientExtension_rawCoherence
    (F : C ⥤ D) (G : D ⥤ H) (L : C ⥤ H) (a : F ⋙ G ≅ L) (X : C) :
    ((functorExtension₂ _ _).obj G).map
        (((functorExtension₂CompWhiskeringLeftToKaroubiIso _ _).app F).hom.app X) ≫
      ((functorExtension₂CompWhiskeringLeftToKaroubiIso _ _).app G).hom.app (F.obj X) ≫
        (toKaroubi H).map (a.hom.app X) =
      (coefficientAssociatorIso F G L a).hom.app ((toKaroubi C).obj X) ≫
        ((functorExtension₂CompWhiskeringLeftToKaroubiIso _ _).app L).hom.app X := by
  unfold coefficientAssociatorIso
  apply Karoubi.hom_ext
  simp only [Functor.comp_obj, Functor.whiskeringLeft_obj_obj, toKaroubi_obj_X,
    Functor.whiskeringRight_obj_obj, Iso.app_hom, Karoubi.comp_f, functorExtension₂_obj_map_f,
    functorExtension₂CompWhiskeringLeftToKaroubiIso_hom_app_app_f, toKaroubi_map_f,
    Functor.mapIso_hom, functorExtension₂_map_app_f, toKaroubi_obj_p, Functor.map_id,
    Category.comp_id]
  change G.map (𝟙 (F.obj X)) ≫ 𝟙 _ ≫ a.hom.app X = a.hom.app X ≫ 𝟙 _
  simp only [Functor.map_id, Category.comp_id, Category.id_comp]

private theorem coefficientSystem_cocycle
    {I : Type*} [Preorder I] {A : I → Type*} [∀ i, Category* (A i)]
    (S : StageSystem A) {i j k m : I} (h : i ≤ j) (h' : j ≤ k) (h'' : k ≤ m)
    (P : Karoubi (A i)) :
    ((functorExtension₂ _ _).obj (S.T h'')).map
        ((coefficientAssociatorIso (S.T h) (S.T h') (S.T (h.trans h')) (S.assoc h h')).hom.app P) ≫
      (coefficientAssociatorIso (S.T (h.trans h')) (S.T h'') (S.T ((h.trans h').trans h''))
        (S.assoc (h.trans h') h'')).hom.app P =
    (coefficientAssociatorIso (S.T h') (S.T h'') (S.T (h'.trans h'')) (S.assoc h' h'')).hom.app
        (((functorExtension₂ _ _).obj (S.T h)).obj P) ≫
      (coefficientAssociatorIso (S.T h) (S.T (h'.trans h'')) (S.T (h.trans (h'.trans h'')))
        (S.assoc h (h'.trans h''))).hom.app P :=
  coefficientExtension_cocycle (S.T h) (S.T h') (S.T h'')
    (S.T (h.trans h')) (S.T (h'.trans h'')) (S.T (h.trans (h'.trans h'')))
    (S.assoc h h') (S.assoc h' h'') (S.assoc (h.trans h') h'')
    (S.assoc h (h'.trans h'')) (S.cocycle h h' h'') P

private theorem coefficientSystem_inclusionTower
    {I : Type*} [Preorder I] [IsDirectedOrder I]
    {A B : I → Type*} [∀ i, Category* (A i)] [∀ i, Category* (B i)]
    (S : StageSystem A) (T : StageSystem B) (J : ∀ i, A i ⥤ B i)
    (b : ∀ {i j} (h : i ≤ j), J i ⋙ T.T h ≅ S.T h ⋙ J j)
    (hb : StageSystem.pairFunctorCoherent S T J b)
    {i j k : I} (h : i ≤ j) (h' : j ≤ k) (P : Karoubi (A i)) :
    ((functorExtension₂ _ _).obj (T.T h')).map
        ((coefficientInclusionComparisonIso (J i) (T.T h) (S.T h) (J j) (b h)).hom.app P) ≫
      (coefficientInclusionComparisonIso (J j) (T.T h') (S.T h') (J k) (b h')).hom.app
        (((functorExtension₂ _ _).obj (S.T h)).obj P) ≫
      ((functorExtension₂ _ _).obj (J k)).map
        ((coefficientAssociatorIso (S.T h) (S.T h') (S.T (h.trans h')) (S.assoc h h')).hom.app P) =
    (coefficientAssociatorIso (T.T h) (T.T h') (T.T (h.trans h')) (T.assoc h h')).hom.app
        (((functorExtension₂ _ _).obj (J i)).obj P) ≫
      (coefficientInclusionComparisonIso (J i) (T.T (h.trans h'))
        (S.T (h.trans h')) (J k) (b (h.trans h'))).hom.app P :=
  coefficientExtension_inclusionTower (S.T h) (S.T h') (S.T (h.trans h'))
    (T.T h) (T.T h') (T.T (h.trans h')) (J i) (J j) (J k)
    (S.assoc h h') (T.assoc h h') (b h) (b h') (b (h.trans h'))
    (hb h h') P

end CategoryTheory.Idempotents

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

namespace CategoryTheory.StageSystem
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

end CategoryTheory.StageSystem

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

namespace AlgebraicGeometry.Scheme

/-- The constructible rational stage before idempotent completion.
Source: sketch32, lines 1204--1207 (blueprint: def-sbc-ambient-complete-coefficient-categories). -/
abbrev pbcConstructibleCompleteStage (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (W : Scheme.{u}) (E : Padic.FiniteCoefficientFields l Ω) : Type (u + 2) :=
  pbcStageCategory l Ω W E

/-- The finite-stage ambient Karoubi category.
Source: sketch32, lines 1204--1207 (blueprint: def-sbc-ambient-complete-coefficient-categories). -/
abbrev pbcAmbientCompleteKaroubiStage (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (W : Scheme.{u}) (E : Padic.FiniteCoefficientFields l Ω) :=
  Idempotents.Karoubi (pbcAmbientCompleteStage l Ω W E)

/-- The finite-stage constructible Karoubi category.
Source: sketch32, lines 1204--1207 (blueprint: def-sbc-ambient-complete-coefficient-categories). -/
abbrev pbcConstructibleCompleteKaroubiStage (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (W : Scheme.{u}) (E : Padic.FiniteCoefficientFields l Ω) :=
  Idempotents.Karoubi (pbcConstructibleCompleteStage l Ω W E)

/-- The canonical finite-stage constructible-to-ambient inclusion after Karoubi completion.
Source: sketch32, lines 1204--1207 (blueprint: def-sbc-ambient-complete-coefficient-categories). -/
@[irreducible] noncomputable def pbcConstructibleCompleteInclusion
    (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
    [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω] (W : Scheme.{u})
    (E : Padic.FiniteCoefficientFields l Ω) :
    pbcConstructibleCompleteKaroubiStage l Ω W E ⥤
      pbcAmbientCompleteKaroubiStage l Ω W E :=
  (Idempotents.functorExtension₂
    (pbcConstructibleCompleteStage l Ω W E) (pbcAmbientCompleteStage l Ω W E)).obj
    (WeilConjectures.pbcRationalInclusion l (pbcFiniteField.{u} l Ω E) W)

variable (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
  [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω] (W : Scheme.{u})
  [IsNoetherian W]
  [hDim : Fact (∃ n : ℕ, topologicalKrullDim W ≤ n)]
  [hInv : Fact (∀ x : W, IsUnit (l : W.presheaf.stalk x))]

variable {E F G : Padic.FiniteCoefficientFields l Ω}

/-- Extend the actual ambient rational tensor to every finite-stage projector.
Source: sketch32, lines 1291--1311
(blueprint: def-sbc-ambient-complete-coefficient-categories). -/
def pbcAmbientCompleteKaroubiTransition (h : E ≤ F) :
    pbcAmbientCompleteKaroubiStage l Ω W E ⥤ pbcAmbientCompleteKaroubiStage l Ω W F :=
  (Idempotents.functorExtension₂
    (pbcAmbientCompleteStage l Ω W E) (pbcAmbientCompleteStage l Ω W F)).obj
      (pbcAmbientCompleteRawTransition l Ω W h)

/-- Extend the existing constructible rational tensor to every finite-stage projector.
Source: sketch32, lines 1291--1311
(blueprint: def-sbc-ambient-complete-coefficient-categories). -/
def pbcConstructibleCompleteKaroubiTransition (h : E ≤ F) :
    pbcConstructibleCompleteKaroubiStage l Ω W E ⥤
      pbcConstructibleCompleteKaroubiStage l Ω W F :=
  (Idempotents.functorExtension₂
    (pbcConstructibleCompleteStage l Ω W E) (pbcConstructibleCompleteStage l Ω W F)).obj
    (pbcScalarExtension l Ω W hDim.out hInv.out h)

/-- Ambient balancing extended by its actual projector-sandwiched components.
Source: sketch32, lines 1291--1311
(blueprint: def-sbc-ambient-complete-coefficient-categories). -/
@[irreducible] def pbcAmbientCompleteKaroubiAssociator (h : E ≤ F) (k : F ≤ G) :
    pbcAmbientCompleteKaroubiTransition l Ω W h ⋙
        pbcAmbientCompleteKaroubiTransition l Ω W k ≅
      pbcAmbientCompleteKaroubiTransition l Ω W (h.trans k) :=
  Idempotents.coefficientAssociatorIso
    (pbcAmbientCompleteRawTransition l Ω W h)
    (pbcAmbientCompleteRawTransition l Ω W k)
    (pbcAmbientCompleteRawTransition l Ω W (h.trans k))
    (pbcAmbientCompleteRawAssociator l Ω W h k)

/-- Constructible balancing extended by its actual projector-sandwiched components.
Source: sketch32, lines 1291--1311
(blueprint: def-sbc-ambient-complete-coefficient-categories). -/
@[irreducible] def pbcConstructibleCompleteKaroubiAssociator (h : E ≤ F) (k : F ≤ G) :
    pbcConstructibleCompleteKaroubiTransition l Ω W h ⋙
        pbcConstructibleCompleteKaroubiTransition l Ω W k ≅
      pbcConstructibleCompleteKaroubiTransition l Ω W (h.trans k) :=
  Idempotents.coefficientAssociatorIso
    (pbcScalarExtension l Ω W hDim.out hInv.out h)
    (pbcScalarExtension l Ω W hDim.out hInv.out k)
    (pbcScalarExtension l Ω W hDim.out hInv.out (h.trans k))
    (pbcScalarAssociator l Ω W hDim.out hInv.out h k)

/-- The Karoubi-extended balanced comparisons inherit both tensor pentagons.
Source: sketch32, lines 1291--1338
(blueprint: def-sbc-ambient-complete-coefficient-categories).
Proof: the composition adapters are identities. Expand Mathlib's extension
components, move the projectors through comparisons by naturality, and cancel
repeated projectors by idempotence. The two raw tensor pentagons give the two
underlying equalities. Faithfulness of Karoubi arrows gives the result. -/
theorem pbcCompleteKaroubi_cocycle (h : E ≤ F) (k : F ≤ G)
    {H : Padic.FiniteCoefficientFields l Ω} (j : G ≤ H) :
    (∀ P : pbcAmbientCompleteKaroubiStage l Ω W E,
      (pbcAmbientCompleteKaroubiTransition l Ω W j).map
          ((pbcAmbientCompleteKaroubiAssociator l Ω W h k).hom.app P) ≫
        (pbcAmbientCompleteKaroubiAssociator l Ω W (h.trans k) j).hom.app P =
      (pbcAmbientCompleteKaroubiAssociator l Ω W k j).hom.app
          ((pbcAmbientCompleteKaroubiTransition l Ω W h).obj P) ≫
        (pbcAmbientCompleteKaroubiAssociator l Ω W h (k.trans j)).hom.app P) ∧
    (∀ P : pbcConstructibleCompleteKaroubiStage l Ω W E,
      (pbcConstructibleCompleteKaroubiTransition l Ω W j).map
          ((pbcConstructibleCompleteKaroubiAssociator l Ω W h k).hom.app P) ≫
        (pbcConstructibleCompleteKaroubiAssociator l Ω W (h.trans k) j).hom.app P =
      (pbcConstructibleCompleteKaroubiAssociator l Ω W k j).hom.app
          ((pbcConstructibleCompleteKaroubiTransition l Ω W h).obj P) ≫
        (pbcConstructibleCompleteKaroubiAssociator l Ω W h (k.trans j)).hom.app P) := by
  constructor
  · intro P
    apply Idempotents.Karoubi.hom_ext
    have ht := Idempotents.coefficientSystem_cocycle
      (pbcAmbientCompleteRawSystem l Ω W) h k j P
    have htf := congrArg (fun f ↦ f.f) ht
    with_unfolding_all
      exact htf
  · intro P
    apply Idempotents.Karoubi.hom_ext
    have ht := Idempotents.coefficientSystem_cocycle
      (pbcScalarSystem l Ω W hDim.out hInv.out) h k j P
    have htf := congrArg (fun f ↦ f.f) ht
    with_unfolding_all
      exact htf

/-- The canonical ambient system on the finite-stage Karoubi categories.
Source: sketch32, lines 1291--1338
(blueprint: def-sbc-ambient-complete-coefficient-categories). -/
@[irreducible] def pbcAmbientCompleteSystem : StageSystem
    (fun E : Padic.FiniteCoefficientFields l Ω ↦ pbcAmbientCompleteKaroubiStage l Ω W E) where
  T h := pbcAmbientCompleteKaroubiTransition l Ω W h
  assoc h k := pbcAmbientCompleteKaroubiAssociator l Ω W h k
  cocycle h k j P := (pbcCompleteKaroubi_cocycle l Ω W h k j).1 P

/-- The canonical constructible system on the finite-stage Karoubi categories.
Source: sketch32, lines 1291--1338
(blueprint: def-sbc-ambient-complete-coefficient-categories). -/
@[irreducible] def pbcConstructibleCompleteSystem : StageSystem
    (fun E : Padic.FiniteCoefficientFields l Ω ↦
      pbcConstructibleCompleteKaroubiStage l Ω W E) where
  T h := pbcConstructibleCompleteKaroubiTransition l Ω W h
  assoc h k := pbcConstructibleCompleteKaroubiAssociator l Ω W h k
  cocycle h k j P := (pbcCompleteKaroubi_cocycle l Ω W h k j).2 P

omit [IsAlgClosure (Padic l) Ω] [IsNoetherian W] hDim hInv in
private theorem pbcCompleteInclusion_localization (E : Padic.FiniteCoefficientFields l Ω) :
    pbcStageLocalization l Ω W E ⋙
        WeilConjectures.pbcRationalInclusion l (pbcFiniteField.{u} l Ω E) W =
      WeilConjectures.pbcConstructibleInclusion l (pbcFiniteField.{u} l Ω E) W ⋙
        pbcAmbientCompleteLocalization l Ω W E := by
  with_unfolding_all
    exact ScalarLocalization.coefficientBetween_localization
      (PbcIntegralRing l (pbcFiniteField.{u} l Ω E)) (pbcStageUniformizer.{u} l Ω E)
      (WeilConjectures.pbcConstructibleInclusion l (pbcFiniteField.{u} l Ω E) W)

private theorem pbcCompleteIntegralInclusion_eq (h : E ≤ F) :
    WeilConjectures.pbcConstructibleInclusion l (pbcFiniteField.{u} l Ω E) W ⋙
        pbcAmbientCompleteIntegralTransition l Ω W h =
      pbcIntegralScalarExtension l Ω W hDim.out hInv.out h ⋙
        WeilConjectures.pbcConstructibleInclusion l (pbcFiniteField.{u} l Ω F) W := by
  apply Functor.hext
  · intro K
    apply ObjectProperty.FullSubcategory.ext
    delta pbcAmbientCompleteIntegralTransition pbcIntegralScalarExtension
    rfl
  · intro K L f
    apply coefficientFullSubcategory_hom_heq
    · apply ObjectProperty.FullSubcategory.ext
      delta pbcAmbientCompleteIntegralTransition pbcIntegralScalarExtension
      rfl
    · apply ObjectProperty.FullSubcategory.ext
      delta pbcAmbientCompleteIntegralTransition pbcIntegralScalarExtension
      rfl
    · unfold pbcAmbientCompleteIntegralTransition pbcIntegralScalarExtension
      rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pbcCompleteIntegralInclusion_associator (h : E ≤ F) (k : F ≤ G)
    (K : pbcIntegralStage l Ω W E) :
    HEq ((WeilConjectures.pbcConstructibleInclusion l (pbcFiniteField.{u} l Ω G) W).map
        ((pbcIntegralScalarAssociator l Ω W hDim.out hInv.out h k).hom.app K))
      ((pbcAmbientCompleteIntegralAssociator l Ω W h k).hom.app
        ((WeilConjectures.pbcConstructibleInclusion l (pbcFiniteField.{u} l Ω E) W).obj K)) := by
  have hc := congrArg (fun α ↦ α.app K)
    (pbcIntegralScalarAssociator_exists l Ω W hDim.out hInv.out h k).exists.choose_spec
  have he := (pbcAmbientCompleteIntegralAssociator_exists l Ω W h k).exists.choose_spec
  have hF :
      (pbcAmbientCompleteIntegralTransition l Ω W h ⋙
        pbcAmbientCompleteIntegralTransition l Ω W k) ⋙
          ObjectProperty.ι (WeilConjectures.IsPbcComplete l (pbcFiniteField.{u} l Ω G) W) =
      ObjectProperty.ι (WeilConjectures.IsPbcComplete l (pbcFiniteField.{u} l Ω E) W) ⋙
        (pbcAmbientScalarExtension l Ω W h ⋙ pbcAmbientScalarExtension l Ω W k) := by
    apply Functor.hext
    · intro K
      delta pbcAmbientCompleteIntegralTransition
      rfl
    · intro K L f
      delta pbcAmbientCompleteIntegralTransition
      rfl
  have hG : pbcAmbientCompleteIntegralTransition l Ω W (h.trans k) ⋙
          ObjectProperty.ι (WeilConjectures.IsPbcComplete l (pbcFiniteField.{u} l Ω G) W) =
      ObjectProperty.ι (WeilConjectures.IsPbcComplete l (pbcFiniteField.{u} l Ω E) W) ⋙
        pbcAmbientScalarExtension l Ω W (h.trans k) := by
    apply Functor.hext
    · intro K
      delta pbcAmbientCompleteIntegralTransition
      rfl
    · intro K L f
      delta pbcAmbientCompleteIntegralTransition
      rfl
  have ha := coefficientNatTrans_app_heq hF hG
    (Functor.whiskerRight
      (pbcAmbientCompleteIntegralAssociator_exists l Ω W h k).exists.choose.hom
      (ObjectProperty.ι (WeilConjectures.IsPbcComplete l (pbcFiniteField.{u} l Ω G) W)))
    (Functor.whiskerLeft
      (ObjectProperty.ι (WeilConjectures.IsPbcComplete l (pbcFiniteField.{u} l Ω E) W))
      (pbcAmbientScalarAssociator l Ω W h k).hom) he
    ((WeilConjectures.pbcConstructibleInclusion l (pbcFiniteField.{u} l Ω E) W).obj K)
  dsimp only [Functor.whiskerRight_app, Functor.whiskerLeft_app,
    ObjectProperty.ι_map, ObjectProperty.ι_obj] at ha
  change HEq _ ((pbcAmbientScalarAssociator l Ω W h k).hom.app K.obj) at ha
  have hx :
      (WeilConjectures.pbcConstructibleInclusion l (pbcFiniteField.{u} l Ω G) W).obj
          ((pbcIntegralScalarExtension l Ω W hDim.out hInv.out h ⋙
            pbcIntegralScalarExtension l Ω W hDim.out hInv.out k).obj K) =
        (pbcAmbientCompleteIntegralTransition l Ω W h ⋙
          pbcAmbientCompleteIntegralTransition l Ω W k).obj
            ((WeilConjectures.pbcConstructibleInclusion l
              (pbcFiniteField.{u} l Ω E) W).obj K) := by
    apply ObjectProperty.FullSubcategory.ext
    delta pbcAmbientCompleteIntegralTransition pbcIntegralScalarExtension
    rfl
  have hy :
      (WeilConjectures.pbcConstructibleInclusion l (pbcFiniteField.{u} l Ω G) W).obj
          ((pbcIntegralScalarExtension l Ω W hDim.out hInv.out (h.trans k)).obj K) =
        (pbcAmbientCompleteIntegralTransition l Ω W (h.trans k)).obj
          ((WeilConjectures.pbcConstructibleInclusion l
            (pbcFiniteField.{u} l Ω E) W).obj K) := by
    apply ObjectProperty.FullSubcategory.ext
    delta pbcAmbientCompleteIntegralTransition pbcIntegralScalarExtension
    rfl
  delta pbcAmbientCompleteIntegralAssociator
  apply coefficientFullSubcategory_hom_heq _ hx hy
  exact (heq_of_eq hc).trans ha.symm

private theorem pbcCompleteRaw_factor (h : E ≤ F) (hne : E ≠ F) :
    pbcAmbientCompleteLocalization l Ω W E ⋙ pbcAmbientCompleteRawTransition l Ω W h =
      pbcAmbientCompleteIntegralTransition l Ω W h ⋙
        pbcAmbientCompleteLocalization l Ω W F := by
  have he : pbcAmbientCompleteRawTransition l Ω W h =
      (pbcAmbientCompleteRaw_exists l Ω W h).exists.choose := by
    delta pbcAmbientCompleteRawTransition
    exact dite_eq_right hne
  exact (congrArg (pbcAmbientCompleteLocalization l Ω W E ⋙ ·) he).trans
    (pbcAmbientCompleteRaw_exists l Ω W h).exists.choose_spec

private theorem pbcConstructibleRaw_factor (h : E ≤ F) (hne : E ≠ F) :
    pbcStageLocalization l Ω W E ⋙ pbcScalarExtension l Ω W hDim.out hInv.out h =
      pbcIntegralScalarExtension l Ω W hDim.out hInv.out h ⋙
        pbcStageLocalization l Ω W F := by
  have he : pbcScalarExtension l Ω W hDim.out hInv.out h =
      (pbcRationalScalarExtension_exists l Ω W hDim.out hInv.out h).exists.choose := by
    delta pbcScalarExtension
    exact dite_eq_right hne
  exact (congrArg (pbcStageLocalization l Ω W E ⋙ ·) he).trans
    (pbcRationalScalarExtension_exists l Ω W hDim.out hInv.out h).exists.choose_spec

private theorem pbcCompleteRawIntegralComparison_id (h : E ≤ F) (hne : E ≠ F)
    (K : WeilConjectures.PbcComplete l (pbcFiniteField.{u} l Ω E) W) :
    HEq ((pbcAmbientCompleteIntegralComparison l Ω W h).hom.app K)
      (𝟙 ((pbcAmbientCompleteRawTransition l Ω W h).obj
        ((pbcAmbientCompleteLocalization l Ω W E).obj K))) := by
  have he : pbcAmbientCompleteRawTransition l Ω W h =
      (pbcAmbientCompleteRaw_exists l Ω W h).exists.choose := by
    delta pbcAmbientCompleteRawTransition
    exact dite_eq_right hne
  exact coefficientIso_hom_app_id
    (congrArg (pbcAmbientCompleteLocalization l Ω W E ⋙ ·) he) rfl
    (pbcAmbientCompleteIntegralComparison l Ω W h)
    (pbcAmbientCompleteRaw_exists l Ω W h).exists.choose_spec
    (by delta pbcAmbientCompleteIntegralComparison
        exact (pbcAmbientCompleteIntegralComparison_exists l Ω W h).exists.choose_spec.2 hne) K

private theorem pbcConstructibleRawIntegralComparison_id (h : E ≤ F) (hne : E ≠ F)
    (K : pbcIntegralStage l Ω W E) :
    HEq ((pbcScalarIntegralComparison l Ω W hDim.out hInv.out h).hom.app K)
      (𝟙 ((pbcScalarExtension l Ω W hDim.out hInv.out h).obj
        ((pbcStageLocalization l Ω W E).obj K))) := by
  have he : pbcScalarExtension l Ω W hDim.out hInv.out h =
      (pbcRationalScalarExtension_exists l Ω W hDim.out hInv.out h).exists.choose := by
    delta pbcScalarExtension
    exact dite_eq_right hne
  exact coefficientIso_hom_app_id (congrArg (pbcStageLocalization l Ω W E ⋙ ·) he) rfl
    (pbcScalarIntegralComparison l Ω W hDim.out hInv.out h)
    (pbcRationalScalarExtension_exists l Ω W hDim.out hInv.out h).exists.choose_spec
    (by
      delta pbcScalarIntegralComparison
      exact (pbcScalarIntegralComparison_exists l Ω W
        hDim.out hInv.out h).exists.choose_spec.2 hne) K

private theorem pbcCompleteRawInclusionFunctor_strict (h : E ≤ F) (e : E ≠ F) :
    WeilConjectures.pbcRationalInclusion l (pbcFiniteField.{u} l Ω E) W ⋙
        pbcAmbientCompleteRawTransition l Ω W h =
      pbcScalarExtension l Ω W hDim.out hInv.out h ⋙
        WeilConjectures.pbcRationalInclusion l (pbcFiniteField.{u} l Ω F) W := by
  have ha := pbcCompleteRaw_factor l Ω W h e
  have hc := pbcConstructibleRaw_factor l Ω W h e
  have hj := pbcCompleteInclusion_localization l Ω W
  have hi := pbcCompleteIntegralInclusion_eq l Ω W h
  have ht := pbcIntegralUniformComplete_isTriangulated l (pbcFiniteField.{u} l Ω E) W
    hDim.out hInv.out
  have := ht.1
  have := ht.2
  let Wloc := Rationalization.W (Submonoid.powers (pbcStageUniformizer.{u} l Ω E))
    (pbcIntegralStage l Ω W E)
  have : (pbcStageLocalization l Ω W E).IsLocalization Wloc :=
    ScalarLocalization.pbcScalarLocalization_isLocalization
      (PbcIntegralRing l (pbcFiniteField.{u} l Ω E)) (pbcIntegralStage l Ω W E)
      (pbcStageUniformizer.{u} l Ω E)
  exact Localization.coefficientSquare_eq
    (pbcStageLocalization l Ω W E) (pbcStageLocalization l Ω W F)
    (pbcAmbientCompleteLocalization l Ω W E) (pbcAmbientCompleteLocalization l Ω W F)
    (WeilConjectures.pbcConstructibleInclusion l (pbcFiniteField.{u} l Ω E) W)
    (WeilConjectures.pbcConstructibleInclusion l (pbcFiniteField.{u} l Ω F) W)
    (pbcIntegralScalarExtension l Ω W hDim.out hInv.out h)
    (pbcAmbientCompleteIntegralTransition l Ω W h)
    (WeilConjectures.pbcRationalInclusion l (pbcFiniteField.{u} l Ω E) W)
    (WeilConjectures.pbcRationalInclusion l (pbcFiniteField.{u} l Ω F) W)
    (pbcScalarExtension l Ω W hDim.out hInv.out h)
    (pbcAmbientCompleteRawTransition l Ω W h)
    (hj E) (hj F) hc ha hi Wloc (fun K ↦ ⟨K.obj, rfl⟩)

private theorem pbcCompleteRawInclusionFunctor_eq (h : E ≤ F) :
    WeilConjectures.pbcRationalInclusion l (pbcFiniteField.{u} l Ω E) W ⋙
        pbcAmbientCompleteRawTransition l Ω W h =
      pbcScalarExtension l Ω W hDim.out hInv.out h ⋙
        WeilConjectures.pbcRationalInclusion l (pbcFiniteField.{u} l Ω F) W := by
  classical
  by_cases e : E = F
  · subst F
    exact coefficientSquare_unit
      (WeilConjectures.pbcRationalInclusion l (pbcFiniteField.{u} l Ω E) W)
      (pbcAmbientCompleteRawTransition l Ω W (le_refl E))
      (pbcScalarExtension l Ω W hDim.out hInv.out (le_refl E))
      (pbcAmbientCompleteRaw_laws l Ω W (le_refl E)
        (le_refl E) (le_refl E)).2.1
      (pbcScalarSystem_units l Ω W hDim.out hInv.out (le_refl E)).1
  · exact pbcCompleteRawInclusionFunctor_strict l Ω W h e

/-- Scalar extension commutes with the raw full inclusion by the identity tensor map.
The heterogeneous equality records the canonical equality of the underlying tensor
objects; it does not permit any other comparison automorphism.
Source: sketch32, lines 1291--1311 and 1419--1426
(blueprint: def-sbc-ambient-complete-coefficient-categories).
Proof: before rationalization both composites are the same tensor object and map
in the complete full subcategory. The normalized unit branches use the same tensor
unit. Localizing the identity comparison gives existence. It fixes every object
component, so natural transformations and inverse equations give uniqueness. -/
theorem pbcCompleteRawInclusionComparison_exists (h : E ≤ F) :
    ∃! b : WeilConjectures.pbcRationalInclusion l (pbcFiniteField.{u} l Ω E) W ⋙
        pbcAmbientCompleteRawTransition l Ω W h ≅
      pbcScalarExtension l Ω W hDim.out hInv.out h ⋙
        WeilConjectures.pbcRationalInclusion l (pbcFiniteField.{u} l Ω F) W,
      ∀ K : pbcConstructibleCompleteStage l Ω W E,
        HEq (b.hom.app K)
          (𝟙 ((pbcAmbientCompleteRawTransition l Ω W h).obj
            ((WeilConjectures.pbcRationalInclusion l (pbcFiniteField.{u} l Ω E) W).obj K))) := by
  exact coefficientIso_identity_exists (pbcCompleteRawInclusionFunctor_eq l Ω W h)

/-- The identity-on-integral-tensor raw inclusion comparison.
Source: sketch32, lines 1291--1311 and 1419--1426
(blueprint: def-sbc-ambient-complete-coefficient-categories). -/
@[irreducible] def pbcCompleteRawInclusionComparison (h : E ≤ F) :
    WeilConjectures.pbcRationalInclusion l (pbcFiniteField.{u} l Ω E) W ⋙
        pbcAmbientCompleteRawTransition l Ω W h ≅
      pbcScalarExtension l Ω W hDim.out hInv.out h ⋙
        WeilConjectures.pbcRationalInclusion l (pbcFiniteField.{u} l Ω F) W :=
  (pbcCompleteRawInclusionComparison_exists l Ω W h).exists.choose

/-- The specified finite-stage inclusion comparison is the actual Karoubi extension
of the identity-on-integral-tensor raw comparison. Mathlib's map on natural
transformations sandwiches each component between the two images of the projector;
the inverse uses the reverse sandwich. The composition comparisons are identities
on the underlying object, projector and arrows.
Source: sketch32, lines 1291--1311 and 1419--1426
(blueprint: def-sbc-ambient-complete-coefficient-categories). -/
@[irreducible] def pbcCompleteKaroubiInclusionComparison (h : E ≤ F) :
    pbcConstructibleCompleteInclusion l Ω W E ⋙
        pbcAmbientCompleteKaroubiTransition l Ω W h ≅
      pbcConstructibleCompleteKaroubiTransition l Ω W h ⋙
        pbcConstructibleCompleteInclusion l Ω W F := by
  with_unfolding_all
    exact Idempotents.coefficientInclusionComparisonIso
      (C₀ := pbcConstructibleCompleteStage l Ω W E)
      (C₁ := pbcConstructibleCompleteStage l Ω W F)
      (D₀ := pbcAmbientCompleteStage l Ω W E)
      (D₁ := pbcAmbientCompleteStage l Ω W F)
      (WeilConjectures.pbcRationalInclusion l (pbcFiniteField.{u} l Ω E) W)
      (pbcAmbientCompleteRawTransition l Ω W h)
      (pbcScalarExtension l Ω W hDim.out hInv.out h)
      (WeilConjectures.pbcRationalInclusion l (pbcFiniteField.{u} l Ω F) W)
      (pbcCompleteRawInclusionComparison l Ω W h)

private theorem pbcCompleteRawInclusionComparison_id (h : E ≤ F)
    (K : pbcConstructibleCompleteStage l Ω W E) :
    HEq ((pbcCompleteRawInclusionComparison l Ω W h).hom.app K)
      (𝟙 ((WeilConjectures.pbcRationalInclusion l (pbcFiniteField.{u} l Ω E) W ⋙
        pbcAmbientCompleteRawTransition l Ω W h).obj K)) := by
  with_unfolding_all
    exact (pbcCompleteRawInclusionComparison_exists l Ω W h).exists.choose_spec K

private theorem pbcCompleteRawAssociator_integral (h : E ≤ F) (k : F ≤ G)
    (he : E ≠ F) (hf : F ≠ G) (hg : E ≠ G)
    (K : WeilConjectures.PbcComplete l (pbcFiniteField.{u} l Ω E) W) :
    HEq ((pbcAmbientCompleteRawAssociator l Ω W h k).hom.app
        ((pbcAmbientCompleteLocalization l Ω W E).obj K))
      ((pbcAmbientCompleteLocalization l Ω W G).map
        ((pbcAmbientCompleteIntegralAssociator l Ω W h k).hom.app K)) := by
  exact coefficientLocalizedAssociator_heq
    (pbcAmbientCompleteLocalization l Ω W E) (pbcAmbientCompleteLocalization l Ω W F)
    (pbcAmbientCompleteLocalization l Ω W G)
    (pbcAmbientCompleteIntegralTransition l Ω W h)
    (pbcAmbientCompleteIntegralTransition l Ω W k)
    (pbcAmbientCompleteIntegralTransition l Ω W (h.trans k))
    (pbcAmbientCompleteRawTransition l Ω W h) (pbcAmbientCompleteRawTransition l Ω W k)
    (pbcAmbientCompleteRawTransition l Ω W (h.trans k))
    (pbcCompleteRaw_factor l Ω W h he) (pbcCompleteRaw_factor l Ω W k hf)
    (pbcCompleteRaw_factor l Ω W (h.trans k) hg)
    (pbcAmbientCompleteIntegralComparison l Ω W h)
    (pbcAmbientCompleteIntegralComparison l Ω W k)
    (pbcAmbientCompleteIntegralComparison l Ω W (h.trans k))
    (pbcCompleteRawIntegralComparison_id l Ω W h he)
    (pbcCompleteRawIntegralComparison_id l Ω W k hf)
    (pbcCompleteRawIntegralComparison_id l Ω W (h.trans k) hg)
    (pbcAmbientCompleteIntegralAssociator l Ω W h k)
    (pbcAmbientCompleteRawAssociator l Ω W h k)
    (by delta pbcAmbientCompleteRawAssociator
        exact (pbcAmbientCompleteRawAssociator_exists l Ω W h k).exists.choose_spec) K

private theorem pbcConstructibleRawAssociator_integral (h : E ≤ F) (k : F ≤ G)
    (he : E ≠ F) (hf : F ≠ G) (hg : E ≠ G) (K : pbcIntegralStage l Ω W E) :
    HEq ((pbcScalarAssociator l Ω W hDim.out hInv.out h k).hom.app
        ((pbcStageLocalization l Ω W E).obj K))
      ((pbcStageLocalization l Ω W G).map
        ((pbcIntegralScalarAssociator l Ω W hDim.out hInv.out h k).hom.app K)) := by
  exact coefficientLocalizedAssociator_heq
    (pbcStageLocalization l Ω W E) (pbcStageLocalization l Ω W F)
    (pbcStageLocalization l Ω W G)
    (pbcIntegralScalarExtension l Ω W hDim.out hInv.out h)
    (pbcIntegralScalarExtension l Ω W hDim.out hInv.out k)
    (pbcIntegralScalarExtension l Ω W hDim.out hInv.out (h.trans k))
    (pbcScalarExtension l Ω W hDim.out hInv.out h)
    (pbcScalarExtension l Ω W hDim.out hInv.out k)
    (pbcScalarExtension l Ω W hDim.out hInv.out (h.trans k))
    (pbcConstructibleRaw_factor l Ω W h he) (pbcConstructibleRaw_factor l Ω W k hf)
    (pbcConstructibleRaw_factor l Ω W (h.trans k) hg)
    (pbcScalarIntegralComparison l Ω W hDim.out hInv.out h)
    (pbcScalarIntegralComparison l Ω W hDim.out hInv.out k)
    (pbcScalarIntegralComparison l Ω W hDim.out hInv.out (h.trans k))
    (pbcConstructibleRawIntegralComparison_id l Ω W h he)
    (pbcConstructibleRawIntegralComparison_id l Ω W k hf)
    (pbcConstructibleRawIntegralComparison_id l Ω W (h.trans k) hg)
    (pbcIntegralScalarAssociator l Ω W hDim.out hInv.out h k)
    (pbcScalarAssociator l Ω W hDim.out hInv.out h k)
    (by delta pbcScalarAssociator
        exact (pbcScalarAssociator_exists l Ω W hDim.out hInv.out h k).exists.choose_spec) K

private theorem pbcCompleteRawAssociator_inclusion (h : E ≤ F) (k : F ≤ G)
    (he : E ≠ F) (hf : F ≠ G) (hg : E ≠ G)
    (K : pbcConstructibleCompleteStage l Ω W E) :
    HEq ((WeilConjectures.pbcRationalInclusion l (pbcFiniteField.{u} l Ω G) W).map
        ((pbcScalarAssociator l Ω W hDim.out hInv.out h k).hom.app K))
      ((pbcAmbientCompleteRawAssociator l Ω W h k).hom.app
        ((WeilConjectures.pbcRationalInclusion l (pbcFiniteField.{u} l Ω E) W).obj K)) := by
  exact coefficientLocalizedInclusion_associator
    (pbcStageLocalization l Ω W E) (pbcStageLocalization l Ω W G)
    (pbcAmbientCompleteLocalization l Ω W E) (pbcAmbientCompleteLocalization l Ω W G)
    (WeilConjectures.pbcConstructibleInclusion l (pbcFiniteField.{u} l Ω E) W)
    (WeilConjectures.pbcConstructibleInclusion l (pbcFiniteField.{u} l Ω G) W)
    (WeilConjectures.pbcRationalInclusion l (pbcFiniteField.{u} l Ω E) W)
    (WeilConjectures.pbcRationalInclusion l (pbcFiniteField.{u} l Ω G) W)
    (pbcIntegralScalarExtension l Ω W hDim.out hInv.out h ⋙
      pbcIntegralScalarExtension l Ω W hDim.out hInv.out k)
    (pbcIntegralScalarExtension l Ω W hDim.out hInv.out (h.trans k))
    (pbcAmbientCompleteIntegralTransition l Ω W h ⋙
      pbcAmbientCompleteIntegralTransition l Ω W k)
    (pbcAmbientCompleteIntegralTransition l Ω W (h.trans k))
    (pbcScalarExtension l Ω W hDim.out hInv.out h ⋙
      pbcScalarExtension l Ω W hDim.out hInv.out k)
    (pbcScalarExtension l Ω W hDim.out hInv.out (h.trans k))
    (pbcAmbientCompleteRawTransition l Ω W h ⋙ pbcAmbientCompleteRawTransition l Ω W k)
    (pbcAmbientCompleteRawTransition l Ω W (h.trans k))
    (pbcIntegralScalarAssociator l Ω W hDim.out hInv.out h k)
    (pbcAmbientCompleteIntegralAssociator l Ω W h k)
    (pbcScalarAssociator l Ω W hDim.out hInv.out h k)
    (pbcAmbientCompleteRawAssociator l Ω W h k)
    (pbcCompleteInclusion_localization l Ω W E) (pbcCompleteInclusion_localization l Ω W G)
    (coefficientFactorization_comp_obj
      (pbcStageLocalization l Ω W E) (pbcStageLocalization l Ω W F)
      (pbcStageLocalization l Ω W G)
      (pbcIntegralScalarExtension l Ω W hDim.out hInv.out h)
      (pbcIntegralScalarExtension l Ω W hDim.out hInv.out k)
      (pbcScalarExtension l Ω W hDim.out hInv.out h)
      (pbcScalarExtension l Ω W hDim.out hInv.out k)
      (pbcConstructibleRaw_factor l Ω W h he) (pbcConstructibleRaw_factor l Ω W k hf))
    (Functor.congr_obj (pbcConstructibleRaw_factor l Ω W (h.trans k) hg))
    (fun K ↦ (Functor.congr_obj (pbcCompleteIntegralInclusion_eq l Ω W k)
      ((pbcIntegralScalarExtension l Ω W hDim.out hInv.out h).obj K)).symm.trans
        (congrArg (pbcAmbientCompleteIntegralTransition l Ω W k).obj
          (Functor.congr_obj (pbcCompleteIntegralInclusion_eq l Ω W h) K).symm))
    (fun K ↦ (Functor.congr_obj
      (pbcCompleteIntegralInclusion_eq l Ω W (h.trans k)) K).symm)
    (pbcConstructibleRawAssociator_integral l Ω W h k he hf hg)
    (pbcCompleteRawAssociator_integral l Ω W h k he hf hg)
    (pbcCompleteIntegralInclusion_associator l Ω W h k)
    (fun K ↦ ⟨K.obj, rfl⟩) K

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pbcCompleteRawInclusion_tower (h : E ≤ F) (k : F ≤ G)
    (K : pbcConstructibleCompleteStage l Ω W E) :
    (pbcAmbientCompleteRawTransition l Ω W k).map
        ((pbcCompleteRawInclusionComparison l Ω W h).hom.app K) ≫
      (pbcCompleteRawInclusionComparison l Ω W k).hom.app
        ((pbcScalarExtension l Ω W hDim.out hInv.out h).obj K) ≫
      (WeilConjectures.pbcRationalInclusion l (pbcFiniteField.{u} l Ω G) W).map
        ((pbcScalarAssociator l Ω W hDim.out hInv.out h k).hom.app K) =
    (pbcAmbientCompleteRawAssociator l Ω W h k).hom.app
        ((WeilConjectures.pbcRationalInclusion l (pbcFiniteField.{u} l Ω E) W).obj K) ≫
      (pbcCompleteRawInclusionComparison l Ω W (h.trans k)).hom.app K := by
  exact coefficientSystem_identityTower_of_units
    (pbcScalarSystem l Ω W hDim.out hInv.out) (pbcAmbientCompleteRawSystem l Ω W)
    (fun E ↦ WeilConjectures.pbcRationalInclusion l (pbcFiniteField.{u} l Ω E) W)
    (fun h ↦ pbcCompleteRawInclusionFunctor_eq l Ω W h)
    (pbcCompleteRawInclusionComparison l Ω W)
    (fun h K ↦ pbcCompleteRawInclusionComparison_id l Ω W h K)
    (fun E ↦ (pbcScalarSystem_units l Ω W hDim.out hInv.out (le_refl E)).1)
    (fun E ↦ (pbcAmbientCompleteRaw_laws l Ω W (le_refl E)
      (le_refl E) (le_refl E)).2.1)
    (fun h ↦ (pbcScalarSystem_units l Ω W hDim.out hInv.out h).2.1)
    (fun h ↦ (pbcScalarSystem_units l Ω W hDim.out hInv.out h).2.2)
    (fun h ↦ (pbcAmbientCompleteRaw_laws l Ω W h (le_refl _) (le_refl _)).2.2.1)
    (fun h ↦ (pbcAmbientCompleteRaw_laws l Ω W h (le_refl _) (le_refl _)).2.2.2.1)
    (fun h k he hf ↦ pbcCompleteRawAssociator_inclusion l Ω W h k he hf
      (by intro e; subst_vars; exact he (le_antisymm h k))) h k K

/-- The fixed finite-stage comparison, expressed through the canonical systems.
Source: sketch32, lines 1291--1311 and 1419--1426
(blueprint: def-sbc-ambient-complete-coefficient-categories). -/
@[irreducible] def pbcCompleteInclusionComparison (h : E ≤ F) :
    pbcConstructibleCompleteInclusion l Ω W E ⋙
        (pbcAmbientCompleteSystem l Ω W).T h ≅
      (pbcConstructibleCompleteSystem l Ω W).T h ⋙
        pbcConstructibleCompleteInclusion l Ω W F := by
  delta pbcAmbientCompleteSystem pbcConstructibleCompleteSystem
  exact pbcCompleteKaroubiInclusionComparison l Ω W h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The comparison is a coherent family for common-stage descent.
Source: sketch32, lines 1291--1338 and 1419--1426
(blueprint: def-sbc-ambient-complete-coefficient-categories).
Proof: before extension the inclusion is identity on integral tensor constructions,
so its unit and tower equations are the tensor unit and balancing equations.
Localize those equations. Extend to projectors by the stated sandwiches; naturality
and idempotence reduce them to the raw equations. -/
theorem pbcCompleteInclusion_coherent (h : E ≤ F) (k : F ≤ G) :
    HEq (pbcCompleteInclusionComparison l Ω W (le_refl E))
      ((pbcConstructibleCompleteInclusion l Ω W E).rightUnitor ≪≫
        (pbcConstructibleCompleteInclusion l Ω W E).leftUnitor.symm) ∧
    (∀ P : pbcConstructibleCompleteKaroubiStage l Ω W E,
      ((pbcAmbientCompleteSystem l Ω W).T k).map
          ((pbcCompleteInclusionComparison l Ω W h).hom.app P) ≫
        (pbcCompleteInclusionComparison l Ω W k).hom.app
          (((pbcConstructibleCompleteSystem l Ω W).T h).obj P) ≫
        (pbcConstructibleCompleteInclusion l Ω W G).map
          (((pbcConstructibleCompleteSystem l Ω W).assoc h k).hom.app P) =
      ((pbcAmbientCompleteSystem l Ω W).assoc h k).hom.app
          ((pbcConstructibleCompleteInclusion l Ω W E).obj P) ≫
        (pbcCompleteInclusionComparison l Ω W (h.trans k)).hom.app P) := by
  constructor
  · with_unfolding_all
      exact Idempotents.coefficientExtension_inclusionUnit
        (WeilConjectures.pbcRationalInclusion l (pbcFiniteField.{u} l Ω E) W)
        (pbcAmbientCompleteRawTransition l Ω W (le_refl E))
        (pbcScalarExtension l Ω W hDim.out hInv.out (le_refl E))
        (pbcCompleteRawInclusionComparison l Ω W (le_refl E))
        (pbcAmbientCompleteRaw_laws l Ω W (le_refl E)
          (le_refl E) (le_refl E)).2.1
        (pbcScalarSystem_units l Ω W hDim.out hInv.out (le_refl E)).1
        (pbcCompleteRawInclusionComparison_id l Ω W (le_refl E))
  · intro P
    apply Idempotents.Karoubi.hom_ext
    have ht := Idempotents.coefficientSystem_inclusionTower
      (pbcScalarSystem l Ω W hDim.out hInv.out) (pbcAmbientCompleteRawSystem l Ω W)
      (fun E ↦ WeilConjectures.pbcRationalInclusion l (pbcFiniteField.{u} l Ω E) W)
      (pbcCompleteRawInclusionComparison l Ω W)
      (fun h k K ↦ pbcCompleteRawInclusion_tower l Ω W h k K) h k P
    have htf := congrArg (fun f ↦ f.f) ht
    with_unfolding_all
      exact htf

set_option linter.unusedSectionVars false in
/-- Pair category of the finite-stage ambient Karoubi categories, followed by outer Karoubi.
Source: sketch32, lines 1291--1338 and 1413--1426
(blueprint: def-sbc-ambient-complete-coefficient-categories). -/
abbrev pbcAmbientCompleteQbarCategory :=
  Idempotents.Karoubi (pbcAmbientCompleteSystem l Ω W).PairCategory

/-- Pair category of finite-stage constructible Karoubi objects, with the outer projector.
Source: sketch32, lines 1291--1338 and 1413--1426
(blueprint: def-sbc-ambient-complete-coefficient-categories). -/
abbrev pbcConstructibleCompleteQbarCategory :=
  Idempotents.Karoubi (pbcConstructibleCompleteSystem l Ω W).PairCategory

/-- The canonical constructible inclusion on the existing common-stage quotient.
The dependency's representative formula conjugates by b at source and target.
Source: sketch32, lines 1291--1338 and 1419--1426
(blueprint: def-sbc-ambient-complete-coefficient-categories). -/
@[irreducible] def pbcCompletePairInclusion :
    (pbcConstructibleCompleteSystem l Ω W).PairCategory ⥤
      (pbcAmbientCompleteSystem l Ω W).PairCategory :=
  StageSystem.coefficientPairFunctor
    (pbcConstructibleCompleteSystem l Ω W) (pbcAmbientCompleteSystem l Ω W)
    (pbcConstructibleCompleteInclusion l Ω W) (pbcCompleteInclusionComparison l Ω W)
    (fun h k P ↦ (pbcCompleteInclusion_coherent l Ω W h k).2 P)

/-- The raw finite-stage categories embed by identity projectors.
Source: sketch32, lines 1192--1207
(blueprint: def-sbc-ambient-complete-coefficient-categories). -/
abbrev pbcRawConstructibleStageToComplete (E : Padic.FiniteCoefficientFields l Ω) :=
  Idempotents.toKaroubi (pbcConstructibleCompleteStage l Ω W E)

/-- The canonical identity-projector scalar comparison, through the named system.
Source: sketch32, lines 1291--1311
(blueprint: def-sbc-ambient-complete-coefficient-categories). -/
@[irreducible] def pbcRawStageToCompleteComparison (h : E ≤ F) :
    pbcRawConstructibleStageToComplete l Ω W E ⋙
        (pbcConstructibleCompleteSystem l Ω W).T h ≅
      (pbcScalarSystem l Ω W hDim.out hInv.out).T h ⋙
        pbcRawConstructibleStageToComplete l Ω W F := by
  delta pbcConstructibleCompleteSystem
  exact (Idempotents.functorExtension₂CompWhiskeringLeftToKaroubiIso
    (pbcConstructibleCompleteStage l Ω W E) (pbcConstructibleCompleteStage l Ω W F)).app
    (pbcScalarExtension l Ω W hDim.out hInv.out h)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical identity-projector comparisons satisfy the descent tower equation.
Source: sketch32, lines 1291--1338 and 1419--1426
(blueprint: def-sbc-ambient-complete-coefficient-categories).
Proof: unfold the canonical systems and use Mathlib's identity-projector comparison.
Its components have underlying identity. Naturality and the projector identities
reduce the tower equation to the same balanced raw tensor associator on both
sides. Faithfulness of Karoubi underlying arrows yields the equation. -/
theorem pbcRawPairToComplete_coherent :
    StageSystem.pairFunctorCoherent (pbcScalarSystem l Ω W hDim.out hInv.out)
      (pbcConstructibleCompleteSystem l Ω W)
      (pbcRawConstructibleStageToComplete l Ω W) (pbcRawStageToCompleteComparison l Ω W) := by
  intro E F G h k P
  apply Idempotents.Karoubi.hom_ext
  have ht := Idempotents.coefficientExtension_rawCoherence
    (pbcScalarExtension l Ω W hDim.out hInv.out h)
    (pbcScalarExtension l Ω W hDim.out hInv.out k)
    (pbcScalarExtension l Ω W hDim.out hInv.out (h.trans k))
    (pbcScalarAssociator l Ω W hDim.out hInv.out h k) P
  have htf := congrArg (fun f ↦ f.f) ht
  with_unfolding_all
    exact htf

/-- The canonical raw-to-nested-pair inclusion on objects and representatives.
Source: sketch32, lines 1291--1338 and 1419--1426
(blueprint: def-sbc-ambient-complete-coefficient-categories). -/
@[irreducible] def pbcRawPairToComplete : pbcQbarCategory l Ω W ⥤
    (pbcConstructibleCompleteSystem l Ω W).PairCategory :=
  StageSystem.coefficientPairFunctor (pbcScalarSystem l Ω W hDim.out hInv.out)
    (pbcConstructibleCompleteSystem l Ω W)
    (pbcRawConstructibleStageToComplete l Ω W) (pbcRawStageToCompleteComparison l Ω W)
    (pbcRawPairToComplete_coherent l Ω W)

/-- Embed the raw Qbar category using identity projectors at both completion steps.
Source: sketch32, lines 1419--1426
(blueprint: def-sbc-ambient-complete-coefficient-categories). -/
def pbcRawQbarToComplete : pbcQbarCategory l Ω W ⥤
    pbcConstructibleCompleteQbarCategory l Ω W :=
  pbcRawPairToComplete l Ω W ⋙ Idempotents.toKaroubi _

/-- The constructible-to-ambient functor on the full nested Karoubi categories.
Objects `((E,(K,p)),e)` are sent to `((E,(j K,j p)),J e)`; both projectors survive.
The finite-stage aliases, normalized tensor systems, quotient representatives and
this outer functor together render the coefficient categories in the node.
Source: sketch32, lines 1191--1228, 1291--1345 and 1412--1438
(blueprint: def-sbc-ambient-complete-coefficient-categories). -/
def pbcConstructibleCompleteQbarInclusion
    (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
    [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω] (W : Scheme.{u})
    [IsNoetherian W]
    [hDim : Fact (∃ n : ℕ, topologicalKrullDim W ≤ n)]
    [hInv : Fact (∀ x : W, IsUnit (l : W.presheaf.stalk x))] :
    pbcConstructibleCompleteQbarCategory l Ω W ⥤ pbcAmbientCompleteQbarCategory l Ω W :=
  (Idempotents.functorExtension₂ _ _).obj (pbcCompletePairInclusion l Ω W)

end AlgebraicGeometry.Scheme
