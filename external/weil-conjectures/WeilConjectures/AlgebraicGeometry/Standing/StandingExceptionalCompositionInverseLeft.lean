/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Standing.StandingExceptionalCompositionInverse
import Mathlib.Lean.Meta.CongrTheorems

/-! # Explicit inverse candidate for the standing exceptional compositor

The inverse compact-support compositor is transposed in the reverse direction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4000
-- Check the derived Hom calculations sequentially.
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale

private def representativeAdjunction (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] :
    Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ)
        (HasCompactification.compactification f) ⊣
      Etale.rightDerivedUpperShriek Λ f :=
  Etale.rightDerivedUpperShriekAdjunction Λ f

private def representativeTranspose (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [CompactSpace Y]
    (K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    {L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))}
    (hL : _root_.DerivedCategory.TStructure.t.plus L) :
    ((rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).obj
      ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.obj K.obj) ⟶ L) ≃
    ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.obj K.obj ⟶
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.obj
        ((Etale.rightDerivedUpperShriek Λ f).obj
          ((comparisonLowerStar (ModuleCat.{u + 1} Λ) Y).rightDerivedFunctor.obj L))) :=
  let e := (fixedCompactSupportComparisonIso Λ (HasCompactification.compactification f)).app K
  e.homFromEquiv.trans
    (((derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) Y).homEquiv _ L).trans
      (((representativeAdjunction Λ f).homEquiv K.obj _).trans
        (Equiv.ofBijective (fun a ↦
          (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.map a)
          (bijective_comparisonUpperStar_mapDerivedCategory_map _ _
            (plus_etaleRightDerivedUpperShriek_obj f hL)))))

private theorem representativeTranspose_left (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] [CompactSpace Y]
    (K K' : _root_.DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    {L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))}
    (hL : _root_.DerivedCategory.TStructure.t.plus L) (a : K ⟶ K')
    (b : (rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).obj
      ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.obj K'.obj) ⟶ L) :
    representativeTranspose Λ f K hL
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).map
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.map a.hom) ≫ b) =
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.map a.hom ≫
        representativeTranspose Λ f K' hL b := by
  have h := (fixedCompactSupportComparisonIso Λ
    (HasCompactification.compactification f)).inv.naturality_assoc a b
  change
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.map
      ((representativeAdjunction Λ f).homEquiv K.obj _
        ((derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) Y).homEquiv _ L
          (((fixedCompactSupportComparisonIso Λ
            (HasCompactification.compactification f)).app K).inv ≫
            (rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).map
              ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.map a.hom) ≫
            b))) =
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.map a.hom ≫
        (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.map
          ((representativeAdjunction Λ f).homEquiv K'.obj _
            ((derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) Y).homEquiv _ L
              (((fixedCompactSupportComparisonIso Λ
                (HasCompactification.compactification f)).app K').inv ≫ b)))
  erw [← h]
  erw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_left,
    Functor.map_comp]
  rfl

private theorem descendTranspose_left
    {A C D : Type*} [Category* A] [Category* C] [Category* D]
    (ν : A ⥤ C) (F : C ⥤ D) {K₀ K₁ : A} {K K' R : C} {L : D}
    (e₀ : ν.obj K₀ ≅ K) (e₁ : ν.obj K₁ ≅ K')
    (E₀ : (F.obj (ν.obj K₀) ⟶ L) → (ν.obj K₀ ⟶ R))
    (E₁ : (F.obj (ν.obj K₁) ⟶ L) → (ν.obj K₁ ⟶ R))
    (a : K ⟶ K') (b : F.obj K' ⟶ L) (a₀ : K₀ ⟶ K₁)
    (ha₀ : ν.map a₀ = e₀.hom ≫ a ≫ e₁.inv)
    (hn : E₀ (F.map (ν.map a₀) ≫ F.map e₁.hom ≫ b) =
      ν.map a₀ ≫ E₁ (F.map e₁.hom ≫ b)) :
    e₀.inv ≫ E₀ (F.map e₀.hom ≫ F.map a ≫ b) =
      a ≫ e₁.inv ≫ E₁ (F.map e₁.hom ≫ b) := by
  rw [ha₀] at hn
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_map_assoc] at hn
  rw [hn]
  simp only [Iso.inv_hom_id_assoc]

private theorem standingHom_apply (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [CompactSpace Y]
    {K : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X K)
    {L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))}
    (hL : _root_.DerivedCategory.TStructure.t.plus L)
    (b : (rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).obj K ⟶ L) :
    let K₀ := Classical.choose hK
    let h₀ := (Classical.choose_spec hK).1
    let e₀ : (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.obj K₀ ≅ K :=
      Classical.choice (Classical.choose_spec hK).2
    standingExceptionalHomEquiv Λ f hK hL b =
      e₀.inv ≫ representativeTranspose Λ f ⟨K₀, h₀⟩ hL
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).map e₀.hom ≫ b) := by
  dsimp only [standingExceptionalHomEquiv, representativeTranspose, representativeAdjunction]
  rfl

private theorem standingHom_left (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [CompactSpace Y]
    {K K' : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X K)
    (hK' : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X K')
    {L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))}
    (hL : _root_.DerivedCategory.TStructure.t.plus L) (a : K ⟶ K')
    (b : (rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).obj K' ⟶ L) :
    standingExceptionalHomEquiv Λ f hK hL
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).map a ≫ b) =
      a ≫ standingExceptionalHomEquiv Λ f hK' hL b := by
  let ν := (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory
  let F := rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f
  let K₀ := Classical.choose hK
  let K₁ := Classical.choose hK'
  let h₀ := (Classical.choose_spec hK).1
  let h₁ := (Classical.choose_spec hK').1
  let e₀ : ν.obj K₀ ≅ K := Classical.choice (Classical.choose_spec hK).2
  let e₁ : ν.obj K₁ ≅ K' := Classical.choice (Classical.choose_spec hK').2
  obtain ⟨a₀, ha₀⟩ := (bijective_comparisonUpperStar_mapDerivedCategory_map
    K₀ K₁ h₁).surjective (e₀.hom ≫ a ≫ e₁.inv)
  have h := representativeTranspose_left Λ f ⟨K₀, h₀⟩ ⟨K₁, h₁⟩ hL
    (ObjectProperty.homMk a₀) (F.map e₁.hom ≫ b)
  change representativeTranspose Λ f ⟨K₀, h₀⟩ hL
    (F.map (ν.map a₀) ≫ F.map e₁.hom ≫ b) =
      ν.map a₀ ≫ representativeTranspose Λ f ⟨K₁, h₁⟩ hL (F.map e₁.hom ≫ b) at h
  change ν.map a₀ = e₀.hom ≫ a ≫ e₁.inv at ha₀
  rw [standingHom_apply, standingHom_apply]
  change e₀.inv ≫ representativeTranspose Λ f ⟨K₀, h₀⟩ hL
      (F.map e₀.hom ≫ F.map a ≫ b) =
    a ≫ e₁.inv ≫ representativeTranspose Λ f ⟨K₁, h₁⟩ hL (F.map e₁.hom ≫ b)
  exact descendTranspose_left ν F e₀ e₁
    (representativeTranspose Λ f ⟨K₀, h₀⟩ hL)
    (representativeTranspose Λ f ⟨K₁, h₁⟩ hL) a b a₀ ha₀ h

private theorem homEquiv_inverse_equation {C : Type*} [Category* C]
    (Q : ObjectProperty C) {R V : C} (hR : Q R) (hV : Q V)
    (E : ∀ K, Q K → ((K ⟶ R) ≃ (K ⟶ V)))
    (hn : ∀ (J K : C) (hJ : Q J) (hK : Q K) (t : J ⟶ K) (a : K ⟶ R),
      E J hJ (t ≫ a) = t ≫ E K hK a) :
    E R hR (𝟙 R) ≫ (E V hV).symm (𝟙 V) = 𝟙 R := by
  apply (E R hR).injective
  rw [hn R V hR hV, Equiv.apply_symm_apply, Category.comp_id]

private def compositeHomEquiv {C D B : Type*} [Category* C] [Category* D] [Category* B]
    (F : C ⥤ D) (G : D ⥤ B) (H : C ⥤ B) (Q : ObjectProperty C)
    {R V : C} {W : D} {L : B} (α : Q.ι ⋙ F ⋙ G ≅ Q.ι ⋙ H)
    (h : ∀ K, Q K → ((H.obj K ⟶ L) ≃ (K ⟶ R)))
    (g : ∀ K, Q K → ((G.obj (F.obj K) ⟶ L) ≃ (F.obj K ⟶ W)))
    (f : ∀ K, Q K → ((F.obj K ⟶ W) ≃ (K ⟶ V)))
    (K : C) (hK : Q K) : (K ⟶ R) ≃ (K ⟶ V) :=
  (h K hK).symm.trans (((α.app ⟨K, hK⟩).symm.homFromEquiv).trans
    ((g K hK).trans (f K hK)))

private theorem compositeHomEquiv_left
    {C D B : Type*} [Category* C] [Category* D] [Category* B]
    (F : C ⥤ D) (G : D ⥤ B) (H : C ⥤ B) (Q : ObjectProperty C)
    {R V : C} {W : D} {L : B} (α : Q.ι ⋙ F ⋙ G ≅ Q.ι ⋙ H)
    (h : ∀ K, Q K → ((H.obj K ⟶ L) ≃ (K ⟶ R)))
    (g : ∀ K, Q K → ((G.obj (F.obj K) ⟶ L) ≃ (F.obj K ⟶ W)))
    (f : ∀ K, Q K → ((F.obj K ⟶ W) ≃ (K ⟶ V)))
    (hh : ∀ (J K : C) (hJ : Q J) (hK : Q K) (t : J ⟶ K)
      (a : H.obj K ⟶ L), h J hJ (H.map t ≫ a) = t ≫ h K hK a)
    (hg : ∀ (J K : C) (hJ : Q J) (hK : Q K) (t : J ⟶ K)
      (a : G.obj (F.obj K) ⟶ L), g J hJ (G.map (F.map t) ≫ a) = F.map t ≫ g K hK a)
    (hf : ∀ (J K : C) (hJ : Q J) (hK : Q K) (t : J ⟶ K)
      (a : F.obj K ⟶ W), f J hJ (F.map t ≫ a) = t ≫ f K hK a)
    (J K : C) (hJ : Q J) (hK : Q K) (t : J ⟶ K) (a : K ⟶ R) :
    compositeHomEquiv F G H Q α h g f J hJ (t ≫ a) =
      t ≫ compositeHomEquiv F G H Q α h g f K hK a := by
  have hs : (h J hJ).symm (t ≫ a) = H.map t ≫ (h K hK).symm a := by
    apply (h J hJ).injective
    rw [Equiv.apply_symm_apply, hh J K hJ hK, Equiv.apply_symm_apply]
  have hn := α.hom.naturality (ObjectProperty.homMk t : ⟨J, hJ⟩ ⟶ ⟨K, hK⟩)
  change G.map (F.map t) ≫ α.hom.app ⟨K, hK⟩ =
    α.hom.app ⟨J, hJ⟩ ≫ H.map t at hn
  change f J hJ (g J hJ (α.hom.app ⟨J, hJ⟩ ≫ (h J hJ).symm (t ≫ a))) =
    t ≫ f K hK (g K hK (α.hom.app ⟨K, hK⟩ ≫ (h K hK).symm a))
  rw [hs, ← Category.assoc, ← hn, Category.assoc, hg J K hJ hK, hf J K hJ hK]

private theorem compositeHom_inverse
    {C D B : Type*} [Category* C] [Category* D] [Category* B]
    (F : C ⥤ D) (G : D ⥤ B) (H : C ⥤ B) (Q : ObjectProperty C)
    {R V : C} {W : D} {L : B} (α : Q.ι ⋙ F ⋙ G ≅ Q.ι ⋙ H)
    (h : ∀ K, Q K → ((H.obj K ⟶ L) ≃ (K ⟶ R)))
    (g : ∀ K, Q K → ((G.obj (F.obj K) ⟶ L) ≃ (F.obj K ⟶ W)))
    (f : ∀ K, Q K → ((F.obj K ⟶ W) ≃ (K ⟶ V)))
    (hR : Q R) (hV : Q V)
    (hh : ∀ (J K : C) (hJ : Q J) (hK : Q K) (t : J ⟶ K)
      (a : H.obj K ⟶ L), h J hJ (H.map t ≫ a) = t ≫ h K hK a)
    (hg : ∀ (J K : C) (hJ : Q J) (hK : Q K) (t : J ⟶ K)
      (a : G.obj (F.obj K) ⟶ L), g J hJ (G.map (F.map t) ≫ a) = F.map t ≫ g K hK a)
    (hf : ∀ (J K : C) (hJ : Q J) (hK : Q K) (t : J ⟶ K)
      (a : F.obj K ⟶ W), f J hJ (F.map t ≫ a) = t ≫ f K hK a) :
    f R hR (g R hR (α.hom.app ⟨R, hR⟩ ≫ (h R hR).symm (𝟙 R))) ≫
      h V hV (α.inv.app ⟨V, hV⟩ ≫ (g V hV).symm ((f V hV).symm (𝟙 V))) = 𝟙 R := by
  let E := compositeHomEquiv F G H Q α h g f
  have hn := compositeHomEquiv_left F G H Q α h g f hh hg hf
  exact homEquiv_inverse_equation Q hR hV E hn

attribute [local irreducible] originCompositionAmbient standingExceptionalHomEquiv
  rightDerivedLowerShriek rightDerivedUpperShriek

-- Instantiating three derived Hom families needs more elaboration than the generic proof.
private theorem standingCompositeHom_inverse (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g] [CompactSpace Y] [CompactSpace S]
    {L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} Λ))}
    (hL : _root_.DerivedCategory.TStructure.t.plus L) :
    let R := (rightDerivedUpperShriek Λ (f ≫ g)).obj L
    let hR := plusEtaleOrigin_rightDerivedUpperShriek_obj (f ≫ g) hL
    let V := (rightDerivedUpperShriek Λ f).obj ((rightDerivedUpperShriek Λ g).obj L)
    let hV := plusEtaleOrigin_rightDerivedUpperShriek_obj f
      (plus_rightDerivedUpperShriek_obj g hL)
    ((standingExceptionalHomEquiv Λ g (hR.rightDerivedLowerShriek_obj f) hL).trans
      (standingExceptionalHomEquiv Λ f hR (plus_rightDerivedUpperShriek_obj g hL)))
      ((originCompositionAmbient Λ f g).hom.app ⟨R, hR⟩ ≫
        (standingExceptionalHomEquiv Λ (f ≫ g) hR hL).symm (𝟙 R)) ≫
      standingExceptionalHomEquiv Λ (f ≫ g) hV hL
        ((originCompositionAmbient Λ f g).inv.app ⟨V, hV⟩ ≫
          (standingExceptionalHomEquiv Λ g (hV.rightDerivedLowerShriek_obj f) hL).symm
            ((standingExceptionalHomEquiv Λ f hV
              (plus_rightDerivedUpperShriek_obj g hL)).symm (𝟙 V))) = 𝟙 R := by
  exact compositeHom_inverse
    (rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f)
    (rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) g)
    (rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) (f ≫ g))
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X)
    (originCompositionAmbient Λ f g)
    (fun K hK ↦ standingExceptionalHomEquiv Λ (f ≫ g)
      (K := K) hK hL)
    (fun K hK ↦ standingExceptionalHomEquiv Λ g
      (K := (rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).obj K)
      (hK.rightDerivedLowerShriek_obj f) hL)
    (fun K hK ↦ standingExceptionalHomEquiv Λ f (K := K) hK
      (plus_rightDerivedUpperShriek_obj g hL))
    (plusEtaleOrigin_rightDerivedUpperShriek_obj (f ≫ g) hL)
    (plusEtaleOrigin_rightDerivedUpperShriek_obj f
      (plus_rightDerivedUpperShriek_obj g hL))
    (fun _ _ hJ hK t a ↦ standingHom_left Λ (f ≫ g) hJ hK
      hL t a)
    (fun _ _ hJ hK t a ↦ standingHom_left Λ g
      (hJ.rightDerivedLowerShriek_obj f) (hK.rightDerivedLowerShriek_obj f)
      hL
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).map t) a)
    (fun _ _ hJ hK t a ↦ standingHom_left Λ f hJ hK
      (plus_rightDerivedUpperShriek_obj g hL) t a)

-- Explicit congruence keeps derived constructions folded when their site witnesses differ.
universe u₁ u₂

private theorem coefficientPiEq {α β : Sort u₁} {P : α → Sort u₂}
    {Q : β → Sort u₂} (h : α = β) (hPQ : HEq P Q) :
    (∀ x, P x) = (∀ x, Q x) := by
  cases h
  cases hPQ
  rfl

open Lean Meta Elab Tactic in
private meta structure CoefficientCongrState where
  proofs : Array (Expr × Expr × Expr) := #[]
  congrs : Array (Expr × Nat × CongrTheorem) := #[]

open Lean Meta Elab Tactic in
private meta partial def coefficientHEq (lhs rhs : Expr) (fuel : Nat := 160) :
    StateRefT CoefficientCongrState MetaM Expr := do
  let lhs := (← instantiateMVars lhs).headBeta
  let rhs := (← instantiateMVars rhs).headBeta
  if lhs == rhs then return ← mkHEqRefl lhs
  if lhs.isFVar then
    if let some v ← lhs.fvarId!.getValue? then
      return ← coefficientHEq v rhs fuel
  if rhs.isFVar then
    if let some v ← rhs.fvarId!.getValue? then
      return ← coefficientHEq lhs v fuel
  if lhs.isLet then
    return ← coefficientHEq (lhs.letBody!.instantiate1 lhs.letValue!) rhs fuel
  if rhs.isLet then
    return ← coefficientHEq lhs (rhs.letBody!.instantiate1 rhs.letValue!) fuel
  let heads := [``standingExceptionalComposition, ``standingExceptionalCompositionInverse]
  if lhs.getAppFn.isConst && heads.contains lhs.getAppFn.constName! then
    if let some lhs' ← unfoldDefinition? lhs then
      return ← coefficientHEq lhs' rhs fuel
  if rhs.getAppFn.isConst && heads.contains rhs.getAppFn.constName! then
    if let some rhs' ← unfoldDefinition? rhs then
      return ← coefficientHEq lhs rhs' fuel
  for (a, b, h) in (← get).proofs do
    if a == lhs && b == rhs then return h
  if fuel == 0 then throwError "coefficient congruence exhausted: {lhs}
{rhs}"
  let next := fuel - 1
  let prove : StateRefT CoefficientCongrState MetaM Expr := do
    if (← isProof lhs) && (← isProof rhs) then
      return ← mkAppM ``proof_irrel_heq #[lhs, rhs]
    match lhs, rhs with
    | .lam n α body _, .lam _ β body' _ =>
      let hα ← mkEqOfHEq (← coefficientHEq α β next)
      let init ← get
      let hfun ← withLocalDeclD n α fun x =>
        withLocalDeclD (n.appendAfter "'") β fun y => do
        withLocalDeclD `hxy (← mkHEq x y) fun hxy => do
          modify fun st => {st with proofs := st.proofs.push (x, y, hxy)}
          let h ← coefficientHEq (body.instantiate1 x) (body'.instantiate1 y) next
          mkLambdaFVars #[x, y, hxy] h
      let congrs := (← get).congrs
      set { init with congrs := congrs }
      let ty ← whnf (← inferType lhs)
      let ty' ← whnf (← inferType rhs)
      let P := mkLambda n .default α ty.bindingBody!
      let Q := mkLambda n .default β ty'.bindingBody!
      return ← mkAppOptM ``Function.hfunext #[some α, some β, some P, some Q,
        some lhs, some rhs, some hα, some hfun]
    | .forallE n α body _, .forallE _ β body' _ =>
      let hα ← mkEqOfHEq (← coefficientHEq α β next)
      let P := mkLambda n .default α body
      let Q := mkLambda n .default β body'
      let hPQ ← coefficientHEq P Q next
      let h ← mkAppOptM ``coefficientPiEq #[some α, some β, some P, some Q,
        some hα, some hPQ]
      return ← mkHEqOfEq h
    | _, _ => pure ()
    let expandProjection (e : Expr) : MetaM Expr := do
      let .proj typeName index major := e.getAppFn | return e
      let info := Lean.getStructureInfo (← getEnv) typeName
      let p ← mkProjection major info.fieldNames[index]!
      return mkAppN p e.getAppArgs
    let lhs' ← expandProjection lhs
    let rhs' ← expandProjection rhs
    if lhs' != lhs || rhs' != rhs then
      return ← coefficientHEq lhs' rhs' next
    let f := lhs.getAppFn
    let g := rhs.getAppFn
    let xs := lhs.getAppArgs
    let ys := rhs.getAppArgs
    if f == g && xs.size == ys.size && !xs.isEmpty then
      let mut found := none
      for (ff, arity, thm) in (← get).congrs do
        if ff == f && arity == xs.size then found := some thm
      let thm? ← match found with
        | some thm => pure (some thm)
        | none => do
          let thm? ← if let .const name levels := f then
            mkHCongrWithArityForConst? name levels xs.size
          else
            try pure (some (← mkHCongrWithArity f xs.size))
            catch _ => pure none
          if let some thm := thm? then
            modify fun st => {st with congrs := st.congrs.push (f, xs.size, thm)}
          pure thm?
      if let some thm := thm? then
        let mut args := #[]
        for i in [:xs.size] do
          let h ← coefficientHEq xs[i]! ys[i]! next
          let h ← if thm.argKinds[i]! == .eq then mkEqOfHEq h else pure h
          args := args ++ #[xs[i]!, ys[i]!, h]
        let h := mkAppN thm.proof args
        let ty ← inferType h
        if ty.isHEq then return h else return ← mkHEqOfEq h
      else
        let ty ← whnf (← inferType lhs)
        let ty' ← whnf (← inferType rhs)
        if ty.isForall && ty'.isForall then
          let lhs' := mkLambda ty.bindingName! .default ty.bindingDomain!
            (mkApp (lhs.liftLooseBVars 0 1) (.bvar 0))
          let rhs' := mkLambda ty'.bindingName! .default ty'.bindingDomain!
            (mkApp (rhs.liftLooseBVars 0 1) (.bvar 0))
          return ← coefficientHEq lhs' rhs' next
    let lhs' ← whnf lhs
    let rhs' ← whnf rhs
    if lhs' != lhs || rhs' != rhs then
      return ← coefficientHEq lhs' rhs' next
    let lhs' := (← unfoldDefinition? lhs).getD lhs
    let rhs' := (← unfoldDefinition? rhs).getD rhs
    if lhs' != lhs || rhs' != rhs then
      return ← coefficientHEq lhs' rhs' next
    throwError "coefficient congruence stuck:
{lhs}
{rhs}"
  let h ← prove
  modify fun st => {st with proofs := st.proofs.push (lhs, rhs, h)}
  return h

-- Allow explicit congruence across the standing derived-category formulas.
/-- One inverse equation for the explicit counit-transpose candidate.
Source: proposition-compatibility-purity-composition--1, exceptional-composition isomorphism, and
proposition-composition-open-restriction-compactifications-f--1, the specified counit formula.
Proof: on bounded-below etale-origin objects, combine the inverse standing Hom
bijection for gf, precomposition by alpha, and the standing Hom bijections for g
and f into E_K : Hom(K,(gf)!L) ≃ Hom(K,f!g!L). The comparison is E_R(id), and the
candidate inverse is E_V.symm(id). Naturality of E in K follows by lifting maps
between etale representatives through fully faithful comparison pullback, then
using naturality of fixedCompactSupportComparisonIso and both adjunction Hom
bijections. Both R=(gf)!L and V=f!g!L lie in this class. The equation E_V(E_V.symm(id))
=id gives b ≫ c=id; applying injectivity of E_R and naturality gives c ≫ b=id.
This theorem records only the displayed one of these two equations. No smoothness,
nonempty-scheme or nonzero-ring hypothesis is used.
(blueprint: lem-route-standing-exceptional-composition-inverse-hom). -/
theorem standingExceptionalComposition_inverse_hom (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y S : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [S.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (S ↘ Spec (.of P.field.k))]
    [QuasiCompact (S ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) (g : Y ⟶ S)
    [f.IsOver (Spec (.of P.field.k))] [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (L : DerivedCategoryBoundedConstructible (ModuleCat.{u + 1} P.Coefficient) S) :
    standingExceptionalComposition P f g L ≫
      standingExceptionalCompositionInverse P f g L = 𝟙 _ := by
  let : Finite P.Ring := Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension P.level P.level_pos
  let : Finite P.Coefficient := inferInstanceAs (Finite (ULift.{u + 1} P.Ring))
  let : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of P.field.k))
  let : IsLocallyNoetherian S :=
    LocallyOfFiniteType.isLocallyNoetherian (S ↘ Spec (.of P.field.k))
  let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace
    (Y ↘ Spec (.of P.field.k))
  let : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace
    (S ↘ Spec (.of P.field.k))
  let hL := L.property.plusEtaleOrigin.plus
  have h := standingCompositeHom_inverse P.Coefficient f g hL
  run_tac Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let h ← Lean.Meta.getLocalDeclFromUserName `h
    let (pf, _) ← (coefficientHEq h.type (← goal.getType) 512).run {}
    let eq ← Lean.Meta.mkAppM ``eq_of_heq #[pf]
    goal.assign (← Lean.Meta.mkAppM ``Eq.mp #[eq, h.toExpr])
    Lean.Elab.Tactic.replaceMainGoal []

end AlgebraicGeometry.ProEtale
