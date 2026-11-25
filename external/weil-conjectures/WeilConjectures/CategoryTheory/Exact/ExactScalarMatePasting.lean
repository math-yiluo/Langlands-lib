/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import Mathlib.CategoryTheory.Adjunction.Mates
import all WeilConjectures.CategoryTheory.DerivedExactSquareComposition

/-! # Pasting scalar mates after exact localization

Source: Stacks Tags 05S7 and 014F; the elementary adjunction mate identities.
(blueprint: lem-weil-pbc-exact-scalar-mate-pasting).
-/

@[expose] public section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

private theorem mate_whisker
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    {F F' : A ⥤ C} {G G' : B ⥤ D}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (t : TwoSquare F L₁ L₂ G)
    (f : F' ⟶ F) (g : G ⟶ G') :
    (mateEquiv a₁ a₂ ((t.whiskerTop f).whiskerBottom g)) =
      Functor.whiskerLeft R₁ f ≫ (mateEquiv a₁ a₂ t) ≫ Functor.whiskerRight g R₂ := by
  ext N
  simp only [mateEquiv_apply, TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app,
    Functor.comp_obj, Category.id_comp, Functor.map_comp, Category.assoc]
  rw [← a₂.unit_naturality_assoc]
  simp only [Functor.comp_map]
  have hg := congrArg R₂.map (g.naturality (a₁.counit.app N))
  simp only [R₂.map_comp] at hg
  rw [← reassoc_of% hg]
  simp

private theorem mate_paste_isIso
    {A B C D E F : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E] [Category F]
    {L₀ : A ⥤ B} {R₀ : B ⥤ A} {L₁ : C ⥤ D} {R₁ : D ⥤ C}
    {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    {U₀₁ : A ⥤ C} {U₁₂ : C ⥤ E} {U₀₂ : A ⥤ E}
    {V₀₁ : B ⥤ D} {V₁₂ : D ⥤ F} {V₀₂ : B ⥤ F}
    (a₀ : L₀ ⊣ R₀) (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
    (k₀₁ : R₀ ⋙ U₀₁ ≅ V₀₁ ⋙ R₁) (k₁₂ : R₁ ⋙ U₁₂ ≅ V₁₂ ⋙ R₂)
    (k₀₂ : R₀ ⋙ U₀₂ ≅ V₀₂ ⋙ R₂)
    (cU : U₀₂ ≅ U₀₁ ⋙ U₁₂) (cV : V₀₂ ≅ V₀₁ ⋙ V₁₂)
    (hk : k₀₂.hom = Functor.whiskerLeft R₀ cU.hom ≫
      (TwoSquare.vComp k₀₁.hom k₁₂.hom) ≫ Functor.whiskerRight cV.inv R₂)
    (h₀₁ : IsIso ((mateEquiv a₀ a₁).symm k₀₁.hom))
    (h₁₂ : IsIso ((mateEquiv a₁ a₂).symm k₁₂.hom)) :
    IsIso ((mateEquiv a₀ a₂).symm k₀₂.hom) := by
  have := h₀₁
  have := h₁₂
  let t₀₁ := (mateEquiv a₀ a₁).symm k₀₁.hom
  let t₁₂ := (mateEquiv a₁ a₂).symm k₁₂.hom
  let t := TwoSquare.hComp t₀₁ t₁₂
  let t' := (t.whiskerTop cU.hom).whiskerBottom cV.inv
  have ht : (mateEquiv a₀ a₂ t') = k₀₂.hom := by
    rw [mate_whisker]
    have hh := mateEquiv_vcomp a₀ a₁ a₂ t₀₁ t₁₂
    dsimp only [t₀₁, t₁₂] at hh
    simp only [Equiv.apply_symm_apply] at hh
    change (mateEquiv a₀ a₂ t) = _ at hh
    rw [hh, hk]
  have ht' : (mateEquiv a₀ a₂).symm k₀₂.hom = t' := by
    rw [← ht]
    exact Equiv.symm_apply_apply _ _
  rw [ht']
  dsimp only [t', t, TwoSquare.hComp, TwoSquare.whiskerTop, TwoSquare.whiskerBottom]
  infer_instance

/-- Pasting exact coefficient squares preserves invertibility of their derived scalar mates.
Source: Stacks Tags 05S7, 014F and the adjunction mate identities.
(blueprint: lem-weil-pbc-exact-scalar-mate-pasting).
Proof: localization carries the specified ordinary pasting identity to the derived
squares. The mate of a pasted square is the pasted mate. The compositor
isomorphisms conjugate this paste, so invertibility of its two factors implies
invertibility of the specified total mate. -/
theorem derivedScalarMatePasting
    {A B C D E F : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E] [Category F]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D] [Abelian E] [Abelian F]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    [HasDerivedCategory D] [HasDerivedCategory E] [HasDerivedCategory F]
    (R₀ : B ⥤ A) (R₁ : D ⥤ C) (R₂ : F ⥤ E)
    (U₀₁ : A ⥤ C) (U₁₂ : C ⥤ E) (U₀₂ : A ⥤ E)
    (V₀₁ : B ⥤ D) (V₁₂ : D ⥤ F) (V₀₂ : B ⥤ F)
    [R₀.Additive] [R₁.Additive] [R₂.Additive]
    [U₀₁.Additive] [U₁₂.Additive] [U₀₂.Additive]
    [V₀₁.Additive] [V₁₂.Additive] [V₀₂.Additive]
    [PreservesFiniteLimits R₀] [PreservesFiniteColimits R₀]
    [PreservesFiniteLimits R₁] [PreservesFiniteColimits R₁]
    [PreservesFiniteLimits R₂] [PreservesFiniteColimits R₂]
    [PreservesFiniteLimits U₀₁] [PreservesFiniteColimits U₀₁]
    [PreservesFiniteLimits U₁₂] [PreservesFiniteColimits U₁₂]
    [PreservesFiniteLimits U₀₂] [PreservesFiniteColimits U₀₂]
    [PreservesFiniteLimits V₀₁] [PreservesFiniteColimits V₀₁]
    [PreservesFiniteLimits V₁₂] [PreservesFiniteColimits V₁₂]
    [PreservesFiniteLimits V₀₂] [PreservesFiniteColimits V₀₂]
    [PreservesFiniteLimits (U₀₁ ⋙ U₁₂)] [PreservesFiniteColimits (U₀₁ ⋙ U₁₂)]
    [PreservesFiniteLimits (V₀₁ ⋙ V₁₂)] [PreservesFiniteColimits (V₀₁ ⋙ V₁₂)]
    {L₀ : DerivedCategory A ⥤ DerivedCategory B}
    {L₁ : DerivedCategory C ⥤ DerivedCategory D}
    {L₂ : DerivedCategory E ⥤ DerivedCategory F}
    (a₀ : L₀ ⊣ R₀.mapDerivedCategory) (a₁ : L₁ ⊣ R₁.mapDerivedCategory)
    (a₂ : L₂ ⊣ R₂.mapDerivedCategory)
    (k₀₁ : R₀ ⋙ U₀₁ ≅ V₀₁ ⋙ R₁) (k₁₂ : R₁ ⋙ U₁₂ ≅ V₁₂ ⋙ R₂)
    (k₀₂ : R₀ ⋙ U₀₂ ≅ V₀₂ ⋙ R₂)
    (cU : U₀₂ ≅ U₀₁ ⋙ U₁₂) (cV : V₀₂ ≅ V₀₁ ⋙ V₁₂)
    (hk : ∀ N, k₀₂.hom.app N ≫ R₂.map (cV.hom.app N) =
      cU.hom.app (R₀.obj N) ≫ U₁₂.map (k₀₁.hom.app N) ≫ k₁₂.hom.app (V₀₁.obj N))
    (h₀₁ : IsIso ((mateEquiv a₀ a₁).symm
      (Functor.mapDerivedCategorySquareIso k₀₁).hom))
    (h₁₂ : IsIso ((mateEquiv a₁ a₂).symm
      (Functor.mapDerivedCategorySquareIso k₁₂).hom)) :
    IsIso ((mateEquiv a₀ a₂).symm
      (Functor.mapDerivedCategorySquareIso k₀₂).hom) := by
  let cUD := Functor.mapDerivedCategoryNatIso cU ≪≫
    (Functor.mapDerivedCategoryCompIso U₀₁ U₁₂).symm
  let cVD := Functor.mapDerivedCategoryNatIso cV ≪≫
    (Functor.mapDerivedCategoryCompIso V₀₁ V₁₂).symm
  refine mate_paste_isIso a₀ a₁ a₂
    (Functor.mapDerivedCategorySquareIso k₀₁) (Functor.mapDerivedCategorySquareIso k₁₂)
    (Functor.mapDerivedCategorySquareIso k₀₂) cUD cVD ?_ h₀₁ h₁₂
  apply NatTrans.ext
  funext N
  have h := Functor.exactSquare_comp_inverse V₀₁ V₁₂ V₀₂ U₀₁ U₁₂ U₀₂ R₀ R₁ R₂
    k₀₁ k₁₂ k₀₂ cV cU hk N
  apply (cancel_mono (R₂.mapDerivedCategory.map (cVD.hom.app N))).mp
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    TwoSquare.vComp, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.assoc]
  rw [← R₂.mapDerivedCategory.map_comp, Iso.inv_hom_id_app]
  simp only [R₂.mapDerivedCategory.map_id]
  simpa [cUD, cVD] using h

end CategoryTheory
