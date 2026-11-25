/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.FiniteStagePairCategory
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Shift.Adjunction
public import Mathlib.CategoryTheory.ObjectProperty.ShiftAdditive
public import WeilConjectures.CategoryTheory.StageSystem.Functor
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Shift.CommShift
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

import Mathlib.CategoryTheory.Shift.Localization
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.Data.Fintype.Order

import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarExtension
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcUniformCompleteTriangulated
import WeilConjectures.AlgebraicGeometry.Pbc.PbcExactCompletionData
import WeilConjectures.AlgebraicGeometry.Pbc.PbcUniformReductionCriterion
import WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleCoefficientHomologyTriangulated
/-! # The actual common-stage additive structure and shift

Source: blueprint `prop-weil-pbc-common-stage-calculus`.
(blueprint: prop-weil-pbc-common-stage-calculus)

These generic constructions apply to the canonical exact scalar-extension system.
They do not substitute an arbitrary system for the coefficient categories.
The sigma used in the representative formula is the adjunction mate of derived
scalar restriction's shift, restricted through the full integral inclusion and
then uniquely descended through rationalization. Thus it is fixed by the actual
tensor construction rather than supplied as an independent comparison.

## Main definitions and statements

* `pbcScalarCommShift`: the tensor-normalized finite-coefficient shift comparison.
* `pbcPairHasShift`: the coherent shift on the actual common-stage quotient.
* `CommonStageCalculusSpec`: the typed clause-by-clause common-stage assertion.
* `commonStageCalculus`: its specialization to the concrete PBC coefficient system.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option linter.unusedSectionVars false
universe c w u v
open CategoryTheory
open scoped ZeroObject
namespace CategoryTheory.ScalarLocalization
open CategoryTheory.Limits

private theorem cscConjugateShift
    {C D : Type*} [Category* C] [Category* D] [HasShift C ℤ] [HasShift D ℤ]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    [L₁.CommShift ℤ] [L₂.CommShift ℤ] [R₁.CommShift ℤ] [R₂.CommShift ℤ]
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) [a₁.CommShift ℤ] [a₂.CommShift ℤ]
    (τ : R₁ ⟶ R₂) [NatTrans.CommShift τ ℤ] :
    NatTrans.CommShift ((conjugateEquiv a₁ a₂).symm τ) ℤ := by
  change NatTrans.CommShift
    (L₂.leftUnitor.inv ≫
      ((Functor.leftUnitor (𝟭 C ⋙ L₂)).inv ≫
        Functor.whiskerRight a₁.unit (𝟭 C ⋙ L₂) ≫
        (Functor.associator (L₁ ⋙ R₁) (𝟭 C) L₂).inv ≫
        Functor.whiskerRight (Functor.associator L₁ R₁ (𝟭 C)).hom L₂ ≫
        Functor.whiskerRight
          (Functor.whiskerLeft L₁ (R₁.rightUnitor.hom ≫ τ ≫ R₂.leftUnitor.inv)) L₂ ≫
        Functor.whiskerRight (Functor.associator L₁ (𝟭 D) R₂).inv L₂ ≫
        (Functor.associator (L₁ ⋙ 𝟭 D) R₂ L₂).hom ≫
        Functor.whiskerLeft (L₁ ⋙ 𝟭 D) a₂.counit ≫
        (L₁ ⋙ 𝟭 D).rightUnitor.hom) ≫ L₁.rightUnitor.hom) ℤ
  infer_instance

private theorem cscAssocShift
    {C₁ C₂ C₃ D₁ D₂ D₃ : Type*}
    [Category* C₁] [Category* C₂] [Category* C₃]
    [Category* D₁] [Category* D₂] [Category* D₃]
    [HasShift C₁ ℤ] [HasShift C₂ ℤ] [HasShift C₃ ℤ]
    [HasShift D₁ ℤ] [HasShift D₂ ℤ] [HasShift D₃ ℤ]
    {F₁₂ : C₁ ⥤ C₂} {F₂₃ : C₂ ⥤ C₃} {F₁₃ : C₁ ⥤ C₃}
    {G₁₂ : D₁ ⥤ D₂} {G₂₃ : D₂ ⥤ D₃} {G₁₃ : D₁ ⥤ D₃}
    {I₁ : C₁ ⥤ D₁} {I₂ : C₂ ⥤ D₂} {I₃ : C₃ ⥤ D₃}
    [F₁₂.CommShift ℤ] [F₂₃.CommShift ℤ] [F₁₃.CommShift ℤ]
    [G₁₂.CommShift ℤ] [G₂₃.CommShift ℤ] [G₁₃.CommShift ℤ]
    [I₁.CommShift ℤ] [I₂.CommShift ℤ] [I₃.CommShift ℤ] [I₃.Faithful]
    (e₁₂ : F₁₂ ⋙ I₂ ≅ I₁ ⋙ G₁₂) (e₂₃ : F₂₃ ⋙ I₃ ≅ I₂ ⋙ G₂₃)
    (e₁₃ : F₁₃ ⋙ I₃ ≅ I₁ ⋙ G₁₃)
    [NatTrans.CommShift e₁₂.hom ℤ] [NatTrans.CommShift e₂₃.hom ℤ]
    [NatTrans.CommShift e₁₃.hom ℤ]
    (α : F₁₂ ⋙ F₂₃ ⟶ F₁₃) (β : G₁₂ ⋙ G₂₃ ⟶ G₁₃)
    [NatTrans.CommShift β ℤ]
    (h : Functor.whiskerRight α I₃ =
      (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft F₁₂ e₂₃.hom ≫
        (Functor.associator _ _ _).inv ≫ Functor.whiskerRight e₁₂.hom G₂₃ ≫
        (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft I₁ β ≫ e₁₃.inv) :
    NatTrans.CommShift α ℤ := by
  have : NatTrans.CommShift (Functor.whiskerRight α I₃) ℤ := by
    rw [h]
    infer_instance
  exact NatTrans.CommShift.of_whiskerRight α I₃

private theorem cscAssocShiftOfWhiskerLeft
    {C₁ C₂ C₃ D₁ D₂ D₃ : Type*}
    [Category* C₁] [Category* C₂] [Category* C₃]
    [Category* D₁] [Category* D₂] [Category* D₃]
    [HasShift C₁ ℤ] [HasShift C₂ ℤ] [HasShift C₃ ℤ]
    [HasShift D₁ ℤ] [HasShift D₂ ℤ] [HasShift D₃ ℤ]
    {F₁₂ : C₁ ⥤ C₂} {F₂₃ : C₂ ⥤ C₃} {F₁₃ : C₁ ⥤ C₃}
    {G₁₂ : D₁ ⥤ D₂} {G₂₃ : D₂ ⥤ D₃} {G₁₃ : D₁ ⥤ D₃}
    {L₁ : C₁ ⥤ D₁} {L₂ : C₂ ⥤ D₂} {L₃ : C₃ ⥤ D₃}
    [F₁₂.CommShift ℤ] [F₂₃.CommShift ℤ] [F₁₃.CommShift ℤ]
    [G₁₂.CommShift ℤ] [G₂₃.CommShift ℤ] [G₁₃.CommShift ℤ]
    [L₁.CommShift ℤ] [L₂.CommShift ℤ] [L₃.CommShift ℤ]
    (e₁₂ : L₁ ⋙ G₁₂ ≅ F₁₂ ⋙ L₂) (e₂₃ : L₂ ⋙ G₂₃ ≅ F₂₃ ⋙ L₃)
    (e₁₃ : L₁ ⋙ G₁₃ ≅ F₁₃ ⋙ L₃)
    [NatTrans.CommShift e₁₂.hom ℤ] [NatTrans.CommShift e₂₃.hom ℤ]
    [NatTrans.CommShift e₁₃.hom ℤ]
    (α : F₁₂ ⋙ F₂₃ ⟶ F₁₃) (β : G₁₂ ⋙ G₂₃ ⟶ G₁₃)
    [NatTrans.CommShift α ℤ]
    (h : ∀ X, β.app (L₁.obj X) =
      G₂₃.map (e₁₂.hom.app X) ≫ e₂₃.hom.app (F₁₂.obj X) ≫
        L₃.map (α.app X) ≫ e₁₃.inv.app X)
    (hL : ∀ X, ∃ (Y : C₁) (f : X ⟶ L₁.obj Y), IsIso (G₁₃.map f)) :
    NatTrans.CommShift β ℤ := by
  have he : Functor.whiskerLeft L₁ β =
      (Functor.associator _ _ _).inv ≫ Functor.whiskerRight e₁₂.hom G₂₃ ≫
        (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft F₁₂ e₂₃.hom ≫
        (Functor.associator _ _ _).inv ≫ Functor.whiskerRight α L₃ ≫ e₁₃.inv := by
    ext X
    simpa only [Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app, NatTrans.comp_app,
      Category.id_comp, Category.comp_id] using h X
  have : NatTrans.CommShift (Functor.whiskerLeft L₁ β) ℤ := by
    rw [he]
    infer_instance
  exact NatTrans.CommShift.of_whiskerLeft β L₁ hL

private theorem cscLiftAssocShift
    {C₁ C₂ C₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
    [HasShift C₁ ℤ] [HasShift C₂ ℤ] [HasShift C₃ ℤ]
    (P₁ : ObjectProperty C₁) (P₂ : ObjectProperty C₂) (P₃ : ObjectProperty C₃)
    [P₁.IsStableUnderShift ℤ] [P₂.IsStableUnderShift ℤ] [P₃.IsStableUnderShift ℤ]
    (G₁₂ : C₁ ⥤ C₂) (G₂₃ : C₂ ⥤ C₃) (G₁₃ : C₁ ⥤ C₃)
    [G₁₂.CommShift ℤ] [G₂₃.CommShift ℤ] [G₁₃.CommShift ℤ]
    (h₁₂ : ∀ K : P₁.FullSubcategory, P₂ (G₁₂.obj K.obj))
    (h₂₃ : ∀ K : P₂.FullSubcategory, P₃ (G₂₃.obj K.obj))
    (h₁₃ : ∀ K : P₁.FullSubcategory, P₃ (G₁₃.obj K.obj)) :
    let F₁₂ := P₂.lift (P₁.ι ⋙ G₁₂) h₁₂
    let F₂₃ := P₃.lift (P₂.ι ⋙ G₂₃) h₂₃
    let F₁₃ := P₃.lift (P₁.ι ⋙ G₁₃) h₁₃
    letI : F₁₂.CommShift ℤ :=
      Functor.CommShift.ofComp (F := F₁₂) (G := P₂.ι) (Iso.refl (P₁.ι ⋙ G₁₂)) ℤ
    letI : F₂₃.CommShift ℤ :=
      Functor.CommShift.ofComp (F := F₂₃) (G := P₃.ι) (Iso.refl (P₂.ι ⋙ G₂₃)) ℤ
    letI : F₁₃.CommShift ℤ :=
      Functor.CommShift.ofComp (F := F₁₃) (G := P₃.ι) (Iso.refl (P₁.ι ⋙ G₁₃)) ℤ
    ∀ (α : F₁₂ ⋙ F₂₃ ⟶ F₁₃) (β : G₁₂ ⋙ G₂₃ ⟶ G₁₃),
      NatTrans.CommShift β ℤ →
      Functor.whiskerRight α P₃.ι = Functor.whiskerLeft P₁.ι β →
        NatTrans.CommShift α ℤ := by
  dsimp only
  let F₁₂ := P₂.lift (P₁.ι ⋙ G₁₂) h₁₂
  let F₂₃ := P₃.lift (P₂.ι ⋙ G₂₃) h₂₃
  let F₁₃ := P₃.lift (P₁.ι ⋙ G₁₃) h₁₃
  let : F₁₂.CommShift ℤ :=
      Functor.CommShift.ofComp (F := F₁₂) (G := P₂.ι) (Iso.refl (P₁.ι ⋙ G₁₂)) ℤ
  let : F₂₃.CommShift ℤ :=
      Functor.CommShift.ofComp (F := F₂₃) (G := P₃.ι) (Iso.refl (P₂.ι ⋙ G₂₃)) ℤ
  let : F₁₃.CommShift ℤ :=
      Functor.CommShift.ofComp (F := F₁₃) (G := P₃.ι) (Iso.refl (P₁.ι ⋙ G₁₃)) ℤ
  intro α β hβ H
  have := hβ
  let e₁₂ : F₁₂ ⋙ P₂.ι ≅ P₁.ι ⋙ G₁₂ := Iso.refl (P₁.ι ⋙ G₁₂)
  let e₂₃ : F₂₃ ⋙ P₃.ι ≅ P₂.ι ⋙ G₂₃ := Iso.refl (P₂.ι ⋙ G₂₃)
  let e₁₃ : F₁₃ ⋙ P₃.ι ≅ P₁.ι ⋙ G₁₃ := Iso.refl (P₁.ι ⋙ G₁₃)
  have : NatTrans.CommShift e₁₂.hom ℤ :=
    Functor.CommShift.ofComp_compatibility (F := F₁₂) (G := P₂.ι) e₁₂ ℤ
  have : NatTrans.CommShift e₂₃.hom ℤ :=
    Functor.CommShift.ofComp_compatibility (F := F₂₃) (G := P₃.ι) e₂₃ ℤ
  have : NatTrans.CommShift e₁₃.hom ℤ :=
    Functor.CommShift.ofComp_compatibility (F := F₁₃) (G := P₃.ι) e₁₃ ℤ
  apply cscAssocShift e₁₂ e₂₃ e₁₃ α β
  ext K
  have hk := congrArg (fun η ↦ η.app K) H
  simpa [e₁₂, e₂₃, e₁₃, F₁₂, F₂₃, F₁₃, ObjectProperty.lift,
    ObjectProperty.ι, inducedFunctor] using hk

private theorem cscLocalizedShift_exists
    {C : Type*} [Category* C] [HasShift C ℤ]
    {D : Type*} [Category* D] [HasShift D ℤ]
    {E : Type*} [Category* E] [HasShift E ℤ]
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W] [L.CommShift ℤ]
    (B : C ⥤ E) [B.CommShift ℤ] (J : D ⥤ E) (e : L ⋙ J ≅ B) :
    ∃! q : J.CommShift ℤ, (letI := q; NatTrans.CommShift e.hom ℤ) := by
  let : Localization.Lifting L W B J := ⟨e⟩
  let q := Functor.commShiftOfLocalization L W ℤ B J
  have hq : letI := q; NatTrans.CommShift e.hom ℤ :=
    NatTrans.commShift_iso_hom_of_localization L W ℤ B J
  refine ⟨q, hq, ?_⟩
  intro t ht
  have square (s : J.CommShift ℤ) (hs : letI := s; NatTrans.CommShift e.hom ℤ)
      (n : ℤ) (X : C) :
      J.map ((L.commShiftIso n).hom.app X) ≫
          (Functor.commShiftIso J (self := s) n).hom.app (L.obj X) ≫
            (shiftFunctor E n).map (e.hom.app X) =
        e.hom.app ((shiftFunctor C n).obj X) ≫ (B.commShiftIso n).hom.app X := by
    let := s
    have := hs
    simpa only [Functor.commShiftIso_comp_hom_app, Category.assoc] using
      NatTrans.shift_app_comm e.hom n X
  apply AlgebraicGeometry.Scheme.pbcKanCommShift_ext t q
  intro n
  apply Iso.ext
  apply Localization.natTrans_ext L W
  intro X
  apply (cancel_epi (J.map ((L.commShiftIso n).hom.app X))).mp
  apply (cancel_mono ((shiftFunctor E n).map (e.hom.app X))).mp
  simpa only [Category.assoc] using (square t ht n X).trans (square q hq n X).symm

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem tensor_eqToHom (R : Type*) [CommRing R] (C : Type*) [Category C]
    [Preadditive C] [Linear R C] (p : R) {X Y : C} (h : X = Y) :
    ((1 : Localization.Away p) ⊗ₜ[R] eqToHom h :
      ScalarLocalization.mk (R := R) (p := p) X ⟶ ⟨Y⟩) =
      eqToHom (congrArg (fun X ↦ ScalarLocalization.mk (R := R) (p := p) X) h) := by
  subst Y
  rfl

private theorem hasShift_ext (C : Type*) [Category C] (s t : HasShift C ℤ)
    (hF : ∀ n : ℤ, (letI := s; shiftFunctor C n) = (letI := t; shiftFunctor C n))
    (hz : ∀ X : C, HEq (letI := s; (shiftFunctorZero C ℤ).hom.app X)
      (letI := t; (shiftFunctorZero C ℤ).hom.app X))
    (ha : ∀ (n m : ℤ) (X : C), HEq (letI := s; (shiftFunctorAdd C n m).hom.app X)
      (letI := t; (shiftFunctorAdd C n m).hom.app X)) : s = t := by
  cases s with
  | mk sf sm =>
    cases t with
    | mk tf tm =>
      have hf : sf = tf := Discrete.functor_ext hF
      cases hf
      have hz' : (letI : HasShift C ℤ := ⟨sf, sm⟩; shiftFunctorZero C ℤ) =
          (letI : HasShift C ℤ := ⟨sf, tm⟩; shiftFunctorZero C ℤ) :=
        Iso.ext (NatTrans.ext (funext (fun X ↦ eq_of_heq (hz X))))
      have ha' (n m : ℤ) :
          (letI : HasShift C ℤ := ⟨sf, sm⟩; shiftFunctorAdd C n m) =
          (letI : HasShift C ℤ := ⟨sf, tm⟩; shiftFunctorAdd C n m) :=
        Iso.ext (NatTrans.ext (funext (fun X ↦ eq_of_heq (ha n m X))))
      congr 1
      apply Functor.Monoidal.ext
      · exact congrArg Iso.inv hz'
      · funext a b
        exact congrArg Iso.inv (ha' a.as b.as)
      · exact congrArg Iso.hom hz'
      · funext a b
        exact congrArg Iso.hom (ha' a.as b.as)

private def tensorShiftZero (R : Type*) [CommRing R] (C : Type*) [Category C]
    [Preadditive C] [Linear R C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive]
    [∀ n : ℤ, (shiftFunctor C n).Linear R] (p : R) :
    map R C p (shiftFunctor C (0 : ℤ)) ≅ 𝟭 (ScalarLocalization R C p) :=
  NatIso.ofComponents
    (fun X ↦ (localization R C p).mapIso ((shiftFunctorZero C ℤ).app X.obj)) (by
      intro X Y f
      change composition R C p _ _ _
          (1 ⊗ₜ[R] (shiftFunctorZero C ℤ).hom.app Y.obj) (mapHom R C p _ _ _ f) =
        composition R C p _ _ _ f (1 ⊗ₜ[R] (shiftFunctorZero C ℤ).hom.app X.obj)
      induction f using TensorProduct.inductionOn with
      | tmul a f =>
        simp [mapHom, composition_tmul,
          (shiftFunctorZero C ℤ).hom.naturality f]
      | add f g hf hg => simp only [map_add, LinearMap.add_apply, hf, hg])

private def tensorShiftAdd (R : Type*) [CommRing R] (C : Type*) [Category C]
    [Preadditive C] [Linear R C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive]
    [∀ n : ℤ, (shiftFunctor C n).Linear R] (p : R) (n m : ℤ) :
    map R C p (shiftFunctor C (n + m)) ≅
      map R C p (shiftFunctor C n) ⋙ map R C p (shiftFunctor C m) :=
  NatIso.ofComponents
    (fun X ↦ (localization R C p).mapIso ((shiftFunctorAdd C n m).app X.obj)) (by
      intro X Y f
      change composition R C p _ _ _
          (1 ⊗ₜ[R] (shiftFunctorAdd C n m).hom.app Y.obj) (mapHom R C p _ _ _ f) =
        composition R C p _ _ _ (mapHom R C p _ _ _ (mapHom R C p _ _ _ f))
          (1 ⊗ₜ[R] (shiftFunctorAdd C n m).hom.app X.obj)
      induction f using TensorProduct.inductionOn with
      | tmul a f =>
        simp [mapHom, composition_tmul,
          (shiftFunctorAdd C n m).hom.naturality f]
      | add f g hf hg => simp only [map_add, LinearMap.add_apply, hf, hg])

private def tensorShiftCore (R : Type*) [CommRing R] (C : Type*) [Category C]
    [Preadditive C] [Linear R C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive]
    [∀ n : ℤ, (shiftFunctor C n).Linear R] (p : R) :
    ShiftMkCore (ScalarLocalization R C p) ℤ where
  F n := map R C p (shiftFunctor C n)
  zero := tensorShiftZero R C p
  add := tensorShiftAdd R C p
  assoc_hom_app a b c X := by
    have h := congrArg (fun f ↦ (localization R C p).map f)
      (shiftFunctorAdd_assoc_hom_app a b c X.obj)
    simp only [shiftFunctorAdd', Iso.trans_hom, eqToIso.hom, NatTrans.comp_app,
      eqToHom_app, Functor.map_comp, eqToHom_map] at h
    simpa [tensorShiftAdd, map, mapHom, localization, shiftFunctorAdd',
      Functor.map_comp, eqToHom_map, tensor_eqToHom, Category.assoc] using h
  zero_add_hom_app n X := by
    have h := congrArg (fun f ↦ (localization R C p).map f)
      (shiftFunctorAdd_zero_add_hom_app n X.obj)
    simp only [Functor.map_comp, eqToHom_map] at h
    simpa [tensorShiftAdd, tensorShiftZero, map, mapHom, localization,
      Functor.map_comp, eqToHom_map, tensor_eqToHom, Category.assoc] using h
  add_zero_hom_app n X := by
    have h := congrArg (fun f ↦ (localization R C p).map f)
      (shiftFunctorAdd_add_zero_hom_app n X.obj)
    simp only [Functor.map_comp, eqToHom_map] at h
    simpa [tensorShiftAdd, tensorShiftZero, map, mapHom, localization,
      Functor.map_comp, eqToHom_map, tensor_eqToHom, Category.assoc] using h

private theorem tensorShift_exists (R : Type*) [CommRing R] (C : Type*) [Category C]
    [Preadditive C] [Linear R C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive]
    [∀ n : ℤ, (shiftFunctor C n).Linear R] (p : R) :
    ∃! s : HasShift (ScalarLocalization R C p) ℤ,
      (letI := s
       (∀ n : ℤ, shiftFunctor (ScalarLocalization R C p) n = map R C p (shiftFunctor C n)) ∧
       (∀ X : ScalarLocalization R C p,
         HEq ((shiftFunctorZero (ScalarLocalization R C p) ℤ).hom.app X)
           ((localization R C p).map ((shiftFunctorZero C ℤ).hom.app X.obj))) ∧
       (∀ (n m : ℤ) (X : ScalarLocalization R C p),
         HEq ((shiftFunctorAdd (ScalarLocalization R C p) n m).hom.app X)
           ((localization R C p).map ((shiftFunctorAdd C n m).hom.app X.obj)))) := by
  let s := hasShiftMk (ScalarLocalization R C p) ℤ (tensorShiftCore R C p)
  refine ⟨s, ⟨fun _ ↦ rfl, fun _ ↦ HEq.rfl, fun _ _ _ ↦ HEq.rfl⟩, ?_⟩
  intro t ht
  apply hasShift_ext _ t s
  · exact ht.1
  · intro X
    exact ht.2.1 X
  · intro n m X
    exact ht.2.2 n m X

private theorem tensorLocalizationShift_exists
    (R : Type*) [CommRing R] (C : Type*) [Category C]
    [Preadditive C] [Linear R C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive]
    [∀ n : ℤ, (shiftFunctor C n).Linear R] (p : R)
    [s : HasShift (ScalarLocalization R C p) ℤ]
    (hn : ∀ n : ℤ, shiftFunctor (ScalarLocalization R C p) n = map R C p (shiftFunctor C n))
    (hz : ∀ X : ScalarLocalization R C p,
      HEq ((shiftFunctorZero (ScalarLocalization R C p) ℤ).hom.app X)
        ((localization R C p).map ((shiftFunctorZero C ℤ).hom.app X.obj)))
    (ha : ∀ (n m : ℤ) (X : ScalarLocalization R C p),
      HEq ((shiftFunctorAdd (ScalarLocalization R C p) n m).hom.app X)
        ((localization R C p).map ((shiftFunctorAdd C n m).hom.app X.obj))) :
    ∃! q : (localization R C p).CommShift ℤ,
      (fun [_qInst : (localization R C p).CommShift ℤ] ↦ ∀ (n : ℤ) (X : C),
        HEq (((localization R C p).commShiftIso n).hom.app X)
          (𝟙 ((localization R C p).obj ((shiftFunctor C n).obj X)))) (_qInst := q) := by
  have hs : s = hasShiftMk (ScalarLocalization R C p) ℤ (tensorShiftCore R C p) :=
    hasShift_ext _ _ _ hn hz ha
  subst s
  let : HasShift (ScalarLocalization R C p) ℤ :=
    hasShiftMk (ScalarLocalization R C p) ℤ (tensorShiftCore R C p)
  let Q := localization R C p
  let e (n : ℤ) : shiftFunctor C n ⋙ Q ≅ Q ⋙ shiftFunctor (ScalarLocalization R C p) n :=
    NatIso.ofComponents (fun X ↦ Iso.refl _) (by
      intro X Y f
      change Q.map ((shiftFunctor C n).map f) ≫ 𝟙 _ =
        𝟙 _ ≫ (map R C p (shiftFunctor C n)).map (Q.map f)
      simp [Q, map, mapHom, localization])
  let q : Q.CommShift ℤ :=
    { commShiftIso := e
      commShiftIso_zero := by
        ext X
        simp only [Functor.CommShift.isoZero_hom_app]
        change 𝟙 _ = Q.map ((shiftFunctorZero C ℤ).hom.app X) ≫
          Q.map ((shiftFunctorZero C ℤ).inv.app X)
        simp only [← Q.map_comp, Iso.hom_inv_id_app, Q.map_id]
      commShiftIso_add := by
        intro n m
        ext X
        simp only [Functor.CommShift.isoAdd_hom_app]
        change 𝟙 _ = Q.map ((shiftFunctorAdd C n m).hom.app X) ≫
          𝟙 _ ≫ (map R C p (shiftFunctor C m)).map (𝟙 _) ≫
            Q.map ((shiftFunctorAdd C n m).inv.app X)
        rw [(map R C p (shiftFunctor C m)).map_id]
        change 𝟙 _ = Q.map ((shiftFunctorAdd C n m).hom.app X) ≫
          𝟙 (Q.obj ((shiftFunctor C n ⋙ shiftFunctor C m).obj X)) ≫
            𝟙 (Q.obj ((shiftFunctor C n ⋙ shiftFunctor C m).obj X)) ≫
              Q.map ((shiftFunctorAdd C n m).inv.app X)
        simp only [Category.id_comp, ← Q.map_comp, Iso.hom_inv_id_app, Q.map_id] }
  refine ⟨q, fun _ _ ↦ HEq.rfl, ?_⟩
  intro t ht
  cases t with
  | mk ti tz ta =>
    have he : ti = e := by
      funext n
      apply Iso.ext
      apply NatTrans.ext
      funext X
      exact eq_of_heq (ht n X)
    subst ti
    rfl

attribute [local irreducible] tensorShiftCore

end CategoryTheory.ScalarLocalization

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable (l : ℕ) [Fact l.Prime] (Ω : Type c) [Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω]
variable {E F G : Padic.FiniteCoefficientFields l Ω}
variable (T : Scheme.{u}) [IsNoetherian T]
  (hdim : ∃ m : ℕ, topologicalKrullDim T ≤ m)
  (hl : ∀ t : T, IsUnit (l : T.presheaf.stalk t))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem cscIntegralTriangulated (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (T : Scheme.{u}) [IsNoetherian T]
    :
    ObjectProperty.IsClosedUnderIsomorphisms.{u + 2, u + 2}
      (C := PbcCompletedDerived T (pbcIntegralDatum l E))
      (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E)) ∧
    ObjectProperty.IsTriangulated.{u + 2, u + 2}
      (C := PbcCompletedDerived T (pbcIntegralDatum l E))
      (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E)) := by
  let d := pbcIntegralDatum l E
  obtain ⟨F, η, hAdd, hShift, hExact, hUnitShift, hComplete⟩ := pbcExactCompletionData T d
  have := hAdd
  let := hShift
  have := hExact
  have := hUnitShift
  have hCompleteEq : PbcIsIntrinsicallyComplete T d = fun K ↦ IsIso (η.app K) := by
    funext K
    exact propext (hComplete K)
  have hc : ObjectProperty.IsClosedUnderIsomorphisms (PbcIsIntrinsicallyComplete T d) ∧
      ObjectProperty.IsTriangulated (PbcIsIntrinsicallyComplete T d) := by
    rw [hCompleteEq]
    exact exactUnitLocus F η
  have := hc.1
  have := hc.2
  have hred (n : ℕ) : ∃ (_ : (pbcCompletedReduction T d n).CommShift ℤ),
      (pbcCompletedReduction T d n).IsTriangulated :=
    (reductionDerivedExistence T (pbcAdicProjection T d n)).choose_spec.choose_spec.2.1
  let (n : ℕ) : (pbcCompletedReduction T d n).CommShift ℤ := (hred n).choose
  let (n : ℕ) : (pbcCompletedReduction T d n).IsTriangulated := (hred n).choose_spec
  let (n : ℕ) : (pbcDerivedRestrict (pbcLevelConstantComparison T d n).hom).CommShift ℤ := by
    dsimp [pbcDerivedRestrict]
    infer_instance
  let (n : ℕ) : (pbcDerivedRestrict (pbcLevelConstantComparison T d n).hom).IsTriangulated := by
    dsimp [pbcDerivedRestrict]
    infer_instance
  let : ∀ n : ℕ, (pbcConstantReduction T d n).CommShift ℤ := fun n ↦ by
    dsimp [pbcConstantReduction]
    infer_instance
  let : ∀ n : ℕ, (pbcConstantReduction T d n).IsTriangulated := fun n ↦ by
    dsimp [pbcConstantReduction]
    infer_instance
  let Q (n : ℕ) := DerivedCategory.homologyProperty
    (@IsConstructibleProEtaleCoefficientModuleSheaf T (ProEtale.PbcQuotient d n) _
      (d.quotientFinite n))
  let (n : ℕ) : (Q n).IsClosedUnderIsomorphisms :=
    (constructibleCoefficientHomology_isTriangulated T (ProEtale.PbcQuotient d n)).1
  let (n : ℕ) : (Q n).IsTriangulated :=
    (constructibleCoefficientHomology_isTriangulated T (ProEtale.PbcQuotient d n)).2
  have hp := uniformProfileLocus
    (fun n : ℕ ↦ DerivedCategory
      (pbcModules T (adicLisseConstantRing T (ProEtale.PbcQuotient d n))))
    (pbcConstantReduction T d) (fun _ ↦ DerivedCategory.TStructure.t) Q
  change ObjectProperty.IsClosedUnderIsomorphisms (PbcUniformReductionProfile T d) ∧
    ObjectProperty.IsTriangulated (PbcUniformReductionProfile T d) at hp
  have := hp.1
  have := hp.2
  have hPredicate : PbcIsBoundedConstructibleComplete T d =
      (PbcIsIntrinsicallyComplete T d ⊓ PbcUniformReductionProfile T d) := by
    funext K
    exact propext (and_congr_right (fun _ ↦ pbcUniformReductionCriterion l E T K))
  change ObjectProperty.IsClosedUnderIsomorphisms (PbcIsBoundedConstructibleComplete T d) ∧
    ObjectProperty.IsTriangulated (PbcIsBoundedConstructibleComplete T d)
  rw [hPredicate]
  exact ⟨inferInstance, inferInstance⟩

/-- Signed reindexing preserves completion, bounded constructible reductions and
compatible etale origins. Source: blueprint orders 1308--1309
(blueprint: prop-weil-pbc-common-stage-calculus).
Proof: tensor with each finite quotient commutes with signed reindexing. Shift
all the bounded local models and all etale witnesses by the same integer; their
bounds translate by that integer and their quotient equations are unchanged.
The Koszul completion tower is shifted termwise, so its limit and unit shift too. -/
@[instance] theorem pbcIntegralStableShift (E : Padic.FiniteCoefficientFields l Ω) :
    ObjectProperty.IsStableUnderShift
      (PbcIsBoundedConstructibleComplete T (pbcStageDatum.{u} l Ω E)) ℤ := by
  have := (cscIntegralTriangulated l (pbcFiniteField.{u} l Ω E) T).2
  infer_instance

/-- The inherited shift remains linear for the actual constant-section action.
Source: blueprint order 1309 (blueprint: prop-weil-pbc-common-stage-calculus).
Proof: scalar multiplication is degreewise multiplication on complexes. Signed
reindexing commutes with it. This passes to roofs in the ambient derived category
and restricts to the full integral subcategory. -/
@[instance] theorem pbcIntegralShiftLinear (E : Padic.FiniteCoefficientFields l Ω) (n : ℤ) :
    (shiftFunctor (PbcBoundedConstructibleComplete T (pbcStageDatum.{u} l Ω E)) n).Linear
      (PbcIntegralRing l (pbcFiniteField.{u} l Ω E)) := by
  let P : ObjectProperty (PbcCompletedDerived T (pbcStageDatum.{u} l Ω E)) :=
    PbcIsBoundedConstructibleComplete T (pbcStageDatum.{u} l Ω E)
  let R := PbcIntegralRing l (pbcFiniteField.{u} l Ω E)
  have : (shiftFunctor P.FullSubcategory n ⋙ P.ι).Linear R :=
    Functor.linear_of_iso R (P.ι.commShiftIso n).symm
  refine ⟨fun f r ↦ P.ι.map_injective ?_⟩
  simp only [Functor.map_smul]

/-- The rational shift is fixed on tensor Homs, including its unit and addition
comparisons. Source: blueprint orders 1308--1309
(blueprint: prop-weil-pbc-common-stage-calculus). -/
def PbcRationalShiftNormalized (E : Padic.FiniteCoefficientFields l Ω)
    (s : HasShift (PbcRationalCategory T (pbcStageDatum.{u} l Ω E)
      (pbcStageUniformizer.{u} l Ω E)) ℤ) : Prop := by
  letI := s
  exact
    (∀ n : ℤ, shiftFunctor
        (PbcRationalCategory T (pbcStageDatum.{u} l Ω E) (pbcStageUniformizer.{u} l Ω E)) n =
      ScalarLocalization.map (PbcIntegralRing l (pbcFiniteField.{u} l Ω E))
        (PbcBoundedConstructibleComplete T (pbcStageDatum.{u} l Ω E))
        (pbcStageUniformizer.{u} l Ω E)
        (shiftFunctor (PbcBoundedConstructibleComplete T (pbcStageDatum.{u} l Ω E)) n)) ∧
    (∀ K : PbcRationalCategory T (pbcStageDatum.{u} l Ω E) (pbcStageUniformizer.{u} l Ω E),
      HEq ((shiftFunctorZero
        (PbcRationalCategory T (pbcStageDatum.{u} l Ω E) (pbcStageUniformizer.{u} l Ω E)) ℤ).hom.app
          K)
        ((pbcRationalization T (pbcStageDatum.{u} l Ω E) (pbcStageUniformizer.{u} l Ω E)).map
          ((shiftFunctorZero
            (PbcBoundedConstructibleComplete T (pbcStageDatum.{u} l Ω E)) ℤ).hom.app K.obj))) ∧
    (∀ (n m : ℤ)
        (K : PbcRationalCategory T (pbcStageDatum.{u} l Ω E) (pbcStageUniformizer.{u} l Ω E)),
      HEq ((shiftFunctorAdd
        (PbcRationalCategory T (pbcStageDatum.{u} l Ω E)
          (pbcStageUniformizer.{u} l Ω E)) n m).hom.app
          K)
        ((pbcRationalization T (pbcStageDatum.{u} l Ω E) (pbcStageUniformizer.{u} l Ω E)).map
          ((shiftFunctorAdd
            (PbcBoundedConstructibleComplete T (pbcStageDatum.{u} l Ω E)) n m).hom.app K.obj)))

/-- Tensoring the integral shift and its comparisons gives the unique normalized
rational shift. Source: blueprint order 1309
(blueprint: prop-weil-pbc-common-stage-calculus).
Proof: extend each integral shift linearly on tensor Homs via ScalarLocalization.map.
Localize the integral zero and addition comparisons. Their coherence holds on
integral maps and extends to all tensors by bilinearity. The object and map
formulas and the component normalizations specify every part of HasShift uniquely. -/
theorem pbcRationalShift_exists (E : Padic.FiniteCoefficientFields l Ω) :
    ∃! s : HasShift (PbcRationalCategory T (pbcStageDatum.{u} l Ω E)
      (pbcStageUniformizer.{u} l Ω E)) ℤ, PbcRationalShiftNormalized l Ω T E s := by
  exact ScalarLocalization.tensorShift_exists
    (PbcIntegralRing l (pbcFiniteField.{u} l Ω E))
    (PbcBoundedConstructibleComplete T (pbcStageDatum.{u} l Ω E))
    (pbcStageUniformizer.{u} l Ω E)

/-- The rational shift has actual signed-reindexing data, uniquely normalized on
integral objects and tensor morphisms. Source: blueprint order 1309
(blueprint: prop-weil-pbc-common-stage-calculus). -/
instance pbcRationalHasShift (E : Padic.FiniteCoefficientFields l Ω) :
    HasShift (PbcRationalCategory T (pbcStageDatum.{u} l Ω E) (pbcStageUniformizer.{u} l Ω E)) ℤ :=
  (pbcRationalShift_exists l Ω T E).exists.choose

/-- The tensor Hom shift is additive. Source: blueprint order 1309
(blueprint: prop-weil-pbc-common-stage-calculus).
Proof: its normalized Hom action is ScalarLocalization.map, whose mapHom is linear. -/
@[instance] theorem pbcRationalShiftAdditive (E : Padic.FiniteCoefficientFields l Ω) (n : ℤ) :
    (shiftFunctor (PbcRationalCategory T (pbcStageDatum.{u} l Ω E)
      (pbcStageUniformizer.{u} l Ω E)) n).Additive := by
  rw [((pbcRationalShift_exists l Ω T E).exists.choose_spec).1 n]
  infer_instance

set_option linter.unusedVariables false in
/-- Localization commutes with shifts through the identity component comparison.
Source: blueprint order 1309 (blueprint: prop-weil-pbc-common-stage-calculus).
Proof: the normalized shift has the same objects and sends 1 tensor f to
1 tensor f[n]. Thus identity components are natural, and the normalized zero
and addition maps give the CommShift laws. The components imply uniqueness. -/
theorem pbcRationalizationShift_exists (E : Padic.FiniteCoefficientFields l Ω) :
    ∃! q : (pbcRationalization T (pbcStageDatum.{u} l Ω E)
        (pbcStageUniformizer.{u} l Ω E)).CommShift ℤ,
      (fun [qInst : (pbcRationalization T (pbcStageDatum.{u} l Ω E)
          (pbcStageUniformizer.{u} l Ω E)).CommShift ℤ] ↦
        ∀ (n : ℤ) (K : PbcBoundedConstructibleComplete T (pbcStageDatum.{u} l Ω E)),
          HEq (((pbcRationalization T (pbcStageDatum.{u} l Ω E)
              (pbcStageUniformizer.{u} l Ω E)).commShiftIso n).hom.app K)
            (𝟙 ((pbcRationalization T (pbcStageDatum.{u} l Ω E)
              (pbcStageUniformizer.{u} l Ω E)).obj
                ((shiftFunctor (PbcBoundedConstructibleComplete T
                  (pbcStageDatum.{u} l Ω E)) n).obj K)))) (qInst := q) := by
  have h := (pbcRationalShift_exists l Ω T E).exists.choose_spec
  exact ScalarLocalization.tensorLocalizationShift_exists
    (PbcIntegralRing l (pbcFiniteField.{u} l Ω E))
    (PbcBoundedConstructibleComplete T (pbcStageDatum.{u} l Ω E))
    (pbcStageUniformizer.{u} l Ω E) h.1 h.2.1 h.2.2

/-- The normalized identity comparison with rationalization.
Source: blueprint order 1309 (blueprint: prop-weil-pbc-common-stage-calculus). -/
instance pbcRationalizationCommShift (E : Padic.FiniteCoefficientFields l Ω) :
    (pbcRationalization T (pbcStageDatum.{u} l Ω E) (pbcStageUniformizer.{u} l Ω E)).CommShift ℤ :=
  (pbcRationalizationShift_exists l Ω T E).exists.choose

/-- Derived scalar restriction has its canonical exact-functor shift comparison.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-common-stage-calculus). -/
instance pbcScalarRestrictCommShift (h : E ≤ F) :
    (pbcDerivedRestrict (pbcCompletedScalarMap l Ω T h)).CommShift ℤ :=
  inferInstanceAs (((pbcRestrict (pbcCompletedScalarMap l Ω T h)).mapDerivedCategory).CommShift ℤ)

/-- The ambient tensor shift comparison is the mate of the canonical shift of
scalar restriction. Source: blueprint order 1307
(blueprint: prop-weil-pbc-common-stage-calculus). -/
instance pbcAmbientScalarCommShift (h : E ≤ F) :
    (pbcAmbientScalarExtension l Ω T h).CommShift ℤ :=
  (pbcDerivedScalarAdjunction (pbcCompletedScalarMap l Ω T h)).leftAdjointCommShift ℤ

/-- The integral tensor comparison is inherited through its fully faithful inclusion.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-common-stage-calculus). -/
instance pbcIntegralScalarCommShift (h : E ≤ F) :
    (pbcIntegralScalarExtension l Ω T hdim hl h).CommShift ℤ :=
  Functor.CommShift.ofComp
    (F := pbcIntegralScalarExtension l Ω T hdim hl h)
    (G := ObjectProperty.ι (PbcIsBoundedConstructibleComplete T (pbcStageDatum.{u} l Ω F)))
    (Iso.refl (ObjectProperty.ι
      (PbcIsBoundedConstructibleComplete T (pbcStageDatum.{u} l Ω E)) ⋙
        pbcAmbientScalarExtension l Ω T h)) ℤ

set_option linter.unusedVariables false in
/-- The rational tensor shift comparison is fixed by the actual integral comparison.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-common-stage-calculus).
Proof: localize the ambient tensor shift component on each integral object and
conjugate by the normalized integral/rational square. Naturality extends from
integral morphisms to their fractions. The integral zero and addition laws
localize, and every rational object is integral, proving uniqueness. -/
theorem pbcScalarShift_exists (h : E ≤ F) :
    ∃! q : (pbcScalarExtension l Ω T hdim hl h).CommShift ℤ,
      (fun [qInst : (pbcScalarExtension l Ω T hdim hl h).CommShift ℤ] ↦
        NatTrans.CommShift (pbcScalarIntegralComparison l Ω T hdim hl h).hom ℤ)
          (qInst := q) := by
  have hE := cscIntegralTriangulated l (pbcFiniteField.{u} l Ω E) T
  have := hE.1
  have := hE.2
  let C := pbcIntegralStage l Ω T E
  let R := PbcIntegralRing l (pbcFiniteField.{u} l Ω E)
  let p := pbcStageUniformizer.{u} l Ω E
  let Q := pbcStageLocalization l Ω T E
  let W := Rationalization.W (Submonoid.powers p) C
  have : Q.IsLocalization W := ScalarLocalization.pbcScalarLocalization_isLocalization R C p
  exact ScalarLocalization.cscLocalizedShift_exists Q W
    (pbcIntegralScalarExtension l Ω T hdim hl h ⋙ pbcStageLocalization l Ω T F)
    (pbcScalarExtension l Ω T hdim hl h) (pbcScalarIntegralComparison l Ω T hdim hl h)

/-- The specified sigma comparison for finite coefficient extension.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-common-stage-calculus). -/
instance pbcScalarCommShift (h : E ≤ F) :
    (pbcScalarExtension l Ω T hdim hl h).CommShift ℤ :=
  (pbcScalarShift_exists l Ω T hdim hl h).exists.choose

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem cscAmbientAssociatorShift (h : E ≤ F) (k : F ≤ G) :
    NatTrans.CommShift (pbcAmbientScalarAssociator l Ω T h k).hom ℤ := by
  have : (pbcDerivedScalarAdjunction (pbcCompletedScalarMap l Ω T h)).CommShift ℤ :=
    Adjunction.commShift_of_rightAdjoint _ ℤ
  have : (pbcDerivedScalarAdjunction (pbcCompletedScalarMap l Ω T k)).CommShift ℤ :=
    Adjunction.commShift_of_rightAdjoint _ ℤ
  have : (pbcDerivedScalarAdjunction
      (pbcCompletedScalarMap l Ω T (h.trans k))).CommShift ℤ :=
    Adjunction.commShift_of_rightAdjoint _ ℤ
  have : NatTrans.CommShift (pbcDerivedRestrictComp (pbcCompletedScalarMap l Ω T h)
      (pbcCompletedScalarMap l Ω T k) (pbcCompletedScalarMap l Ω T (h.trans k))
      (pbcCompletedScalarMap_comp l Ω T h k)).hom ℤ := by
    dsimp only [pbcDerivedRestrictComp, Iso.trans_hom, Iso.symm_hom]
    infer_instance
  exact ScalarLocalization.cscConjugateShift _ _ _

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem cscIntegralAssociatorShift (h : E ≤ F) (k : F ≤ G) :
    NatTrans.CommShift (pbcIntegralScalarAssociator l Ω T hdim hl h k).hom ℤ := by
  exact ScalarLocalization.cscLiftAssocShift
    (PbcIsBoundedConstructibleComplete T (pbcStageDatum.{u} l Ω E))
    (PbcIsBoundedConstructibleComplete T (pbcStageDatum.{u} l Ω F))
    (PbcIsBoundedConstructibleComplete T (pbcStageDatum.{u} l Ω G))
    (pbcAmbientScalarExtension l Ω T h) (pbcAmbientScalarExtension l Ω T k)
    (pbcAmbientScalarExtension l Ω T (h.trans k))
    (pbcAmbientScalarExtension_preserves l Ω T h hdim hl)
    (pbcAmbientScalarExtension_preserves l Ω T k hdim hl)
    (pbcAmbientScalarExtension_preserves l Ω T (h.trans k) hdim hl)
    (pbcIntegralScalarAssociator l Ω T hdim hl h k).hom
    (pbcAmbientScalarAssociator l Ω T h k).hom (cscAmbientAssociatorShift l Ω T h k)
    (pbcIntegralScalarAssociator_exists l Ω T hdim hl h k).exists.choose_spec

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Tensor balancing commutes with the normalized sigma comparisons.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-common-stage-calculus).
Proof: the ambient associator is the mate of identity-on-sections restriction
composition, which commutes with signed reindexing. Restrict and rationalize
that equation; the normalizations of both comparisons preserve it. -/
@[instance] theorem pbcScalarAssociatorCommShift (h : E ≤ F) (k : F ≤ G) :
    NatTrans.CommShift (pbcScalarAssociator l Ω T hdim hl h k).hom ℤ := by
  have := cscIntegralAssociatorShift l Ω T hdim hl h k
  have hcomp (E F : Padic.FiniteCoefficientFields l Ω) (h : E ≤ F) :
      NatTrans.CommShift (pbcScalarIntegralComparison l Ω T hdim hl h).hom ℤ :=
    (pbcScalarShift_exists l Ω T hdim hl h).exists.choose_spec
  have := hcomp E F h
  have := hcomp F G k
  have := hcomp E G (h.trans k)
  exact ScalarLocalization.cscAssocShiftOfWhiskerLeft
    (pbcScalarIntegralComparison l Ω T hdim hl h)
    (pbcScalarIntegralComparison l Ω T hdim hl k)
    (pbcScalarIntegralComparison l Ω T hdim hl (h.trans k))
    (pbcIntegralScalarAssociator l Ω T hdim hl h k).hom
    (pbcScalarAssociator l Ω T hdim hl h k).hom
    (pbcScalarAssociator_exists l Ω T hdim hl h k).exists.choose_spec
    (fun X ↦ ⟨X.obj, 𝟙 _, by
      change IsIso ((pbcScalarExtension l Ω T hdim hl (h.trans k)).map (𝟙 X))
      rw [CategoryTheory.Functor.map_id]
      infer_instance⟩)

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- The actual raw rational stages have finite biproducts and a zero object.
Source: blueprint orders 1308--1309 (blueprint: prop-weil-pbc-common-stage-calculus).
Proof: the zero complex and finite sums satisfy all three defining integral
conditions: their reductions, local finite models and etale witnesses are the
corresponding sums. Finite sums commute with the Koszul limit. Their inclusion
and projection maps obey the biproduct equations in the full subcategory.
Tensor these maps with one; the same five equations hold in the raw localization. -/
@[instance] theorem pbcStageFiniteBiproducts (E : Padic.FiniteCoefficientFields l Ω) :
    Limits.HasFiniteBiproducts (PbcRationalCategory T (pbcStageDatum.{u} l Ω E)
      (pbcStageUniformizer.{u} l Ω E)) := by
  have h := cscIntegralTriangulated l (pbcFiniteField.{u} l Ω E) T
  have := h.1
  have := h.2
  let Q := pbcRationalization T (pbcStageDatum.{u} l Ω E) (pbcStageUniformizer.{u} l Ω E)
  have : Q.EssSurj := ⟨fun K ↦ ⟨K.obj, ⟨Iso.refl _⟩⟩⟩
  have := Functor.hasFiniteProducts_of_additive_of_essSurj Q
  exact Limits.HasFiniteBiproducts.of_hasFiniteProducts

end AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CategoryTheory.StageSystem

variable {I : Type w} [Preorder I] [IsDirectedOrder I]
    {C : I → Type u} [∀ i, Category.{v} (C i)] (S : StageSystem C)

section Shift
variable [stageShift : ∀ i, HasShift (C i) ℤ]
    [transitionShift : ∀ {i j : I} (h : i ≤ j), (S.T h).CommShift ℤ]
    [associatorShift : ∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k),
      NatTrans.CommShift (S.assoc h h').hom ℤ]
include associatorShift

/-- Compatibility of the shift comparisons with associators.
Source: blueprint scalar-extension shifts and common-stage shift
(blueprint: prop-weil-pbc-common-stage-calculus).
Proof: expand the composite functor's shift comparison in the CommShift equation
for the associator. Its component equation is exactly the displayed compatibility. -/
theorem pbcStageShift_coherence (n : ℤ) {i j k : I}
    (h : i ≤ j) (h' : j ≤ k) (X : C i) :
    (S.T h').map (((S.T h).commShiftIso n).hom.app X) ≫
      ((S.T h').commShiftIso n).hom.app ((S.T h).obj X) ≫
        (shiftFunctor (C k) n).map ((S.assoc h h').hom.app X) =
    (S.assoc h h').hom.app ((shiftFunctor (C i) n).obj X) ≫
      ((S.T (h.trans h')).commShiftIso n).hom.app X := by
  simpa only [Functor.commShiftIso_comp_hom_app, Functor.comp_obj,
    Category.assoc] using
    NatTrans.shift_app_comm (S.assoc h h').hom n X

/-- Shifting each finite stage gives a morphism of the actual stage system.
Source: blueprint common-stage calculus
(blueprint: prop-weil-pbc-common-stage-calculus). -/
def pbcStageShift (n : ℤ) : S.Morphism S where
  Φ i := shiftFunctor (C i) n
  β h := (S.T h).commShiftIso n
  coh h h' X := pbcStageShift_coherence S n h h' X

/-- The induced shift sends (E,K) literally to (E,K[n]) and acts on representatives
by the prescribed shift-comparison conjugation.
Source: blueprint common-stage calculus
(blueprint: prop-weil-pbc-common-stage-calculus). -/
def pbcPairShift (n : ℤ) : S.PairCategory ⥤ S.PairCategory :=
  (pbcStageShift S n).functor

/-- Naturality of the stagewise zero-shift comparison on common-stage classes.
Source: blueprint common-stage calculus
(blueprint: prop-weil-pbc-common-stage-calculus).
Proof: represent f at one stage. The CommShift zero axiom identifies its conjugated
shift with f, using naturality of the finite-stage zero comparison. Applying the
common-stage quotient yields the displayed equation. -/
theorem pbcPairShiftZero_naturality {X Y : S.PairCategory} (f : X ⟶ Y) :
    (pbcPairShift S 0).map f ≫
      (S.ι Y.stage).map ((shiftFunctorZero (C Y.stage) ℤ).hom.app Y.obj) =
    (S.ι X.stage).map ((shiftFunctorZero (C X.stage) ℤ).hom.app X.obj) ≫ f := by
  induction f using PairCategory.hom_induction with
  | h k hX hY u =>
    change (pbcStageShift S 0).functor.map (PairCategory.mkHom k hX hY u) ≫ _ = _
    rw [Morphism.functor_map_mkHom, ι_map_eq hY, ι_map_eq hX]
    rw [PairCategory.mkHom_comp_mkHom, PairCategory.mkHom_comp_mkHom]
    congr 1
    dsimp only [Morphism.functor, pbcStageShift]
    simp [Morphism.mapAt, Functor.commShiftIso_zero,
      Functor.CommShift.isoZero, Category.assoc, ← Functor.map_comp]

/-- The zero comparison is the actual image of the finite-stage zero comparison.
Source: blueprint common-stage calculus
(blueprint: prop-weil-pbc-common-stage-calculus). -/
def pbcPairShiftZero : pbcPairShift S 0 ≅ 𝟭 S.PairCategory :=
  NatIso.ofComponents
    (fun X ↦ (S.ι X.stage).mapIso ((shiftFunctorZero (C X.stage) ℤ).app X.obj))
    (fun f ↦ pbcPairShiftZero_naturality S f)

/-- Naturality of the stagewise addition comparison on morphism classes.
Source: blueprint common-stage calculus
(blueprint: prop-weil-pbc-common-stage-calculus).
Proof: use one representative of f. The CommShift addition axiom rewrites both
composites into the same shifted representative. Finite-stage naturality of
shiftFunctorAdd proves equality before passing to the common-stage quotient. -/
theorem pbcPairShiftAdd_naturality (n m : ℤ) {X Y : S.PairCategory} (f : X ⟶ Y) :
    (pbcPairShift S (n + m)).map f ≫
      (S.ι Y.stage).map ((shiftFunctorAdd (C Y.stage) n m).hom.app Y.obj) =
    (S.ι X.stage).map ((shiftFunctorAdd (C X.stage) n m).hom.app X.obj) ≫
      (pbcPairShift S n ⋙ pbcPairShift S m).map f := by
  induction f using PairCategory.hom_induction with
  | h k hX hY u =>
    change (pbcStageShift S (n + m)).functor.map (PairCategory.mkHom k hX hY u) ≫ _ =
      _ ≫ (pbcStageShift S m).functor.map
        ((pbcStageShift S n).functor.map (PairCategory.mkHom k hX hY u))
    rw [Morphism.functor_map_mkHom, Morphism.functor_map_mkHom,
      Morphism.functor_map_mkHom, ι_map_eq hY, ι_map_eq hX]
    rw [PairCategory.mkHom_comp_mkHom, PairCategory.mkHom_comp_mkHom]
    congr 1
    dsimp only [Morphism.functor, pbcStageShift]
    simp [Morphism.mapAt, Functor.commShiftIso_add,
      Functor.CommShift.isoAdd_hom_app, Functor.CommShift.isoAdd_inv_app,
      Category.assoc, ← Functor.map_comp]
    simp only [Functor.map_comp, Category.assoc]

/-- The addition comparison is the actual image of the finite-stage comparison.
Source: blueprint common-stage calculus
(blueprint: prop-weil-pbc-common-stage-calculus). -/
def pbcPairShiftAdd (n m : ℤ) :
    pbcPairShift S (n + m) ≅ pbcPairShift S n ⋙ pbcPairShift S m :=
  NatIso.ofComponents
    (fun X ↦ (S.ι X.stage).mapIso ((shiftFunctorAdd (C X.stage) n m).app X.obj))
    (fun f ↦ pbcPairShiftAdd_naturality S n m f)

/-- Coherence of the actual descended shift comparisons.
Source: blueprint common-stage calculus
(blueprint: prop-weil-pbc-common-stage-calculus).
Proof: each comparison component is the stage inclusion applied to the corresponding
finite-stage shift comparison. The shift of an included map is its included finite-stage
shift. Thus the three equations are the associativity and two unit equations of the
finite-stage HasShift structure, preserved by the inclusion functor. -/
theorem pbcPairShift_laws :
    (∀ (a b c : ℤ) (X : S.PairCategory),
      (pbcPairShiftAdd S (a + b) c).hom.app X ≫
        (pbcPairShift S c).map ((pbcPairShiftAdd S a b).hom.app X) =
      eqToHom (by rw [add_assoc]) ≫ (pbcPairShiftAdd S a (b + c)).hom.app X ≫
        (pbcPairShiftAdd S b c).hom.app ((pbcPairShift S a).obj X)) ∧
    (∀ (n : ℤ) (X : S.PairCategory),
      (pbcPairShiftAdd S 0 n).hom.app X =
        eqToHom (by dsimp; rw [zero_add]) ≫
          (pbcPairShift S n).map ((pbcPairShiftZero S).inv.app X)) ∧
    (∀ (n : ℤ) (X : S.PairCategory),
      (pbcPairShiftAdd S n 0).hom.app X =
        eqToHom (by dsimp; rw [add_zero]) ≫
          (pbcPairShiftZero S).inv.app ((pbcPairShift S n).obj X)) := by
  constructor
  · intro a b c X
    have h := congrArg (fun f ↦ (S.ι X.stage).map f)
      (shiftFunctorAdd_assoc_hom_app a b c X.obj)
    simpa [pbcPairShiftAdd, pbcPairShift, pbcPairShiftZero,
      Morphism.functor_map_ι, pbcStageShift, shiftFunctorAdd',
      Functor.map_comp, eqToHom_map,
      Morphism.functor_obj] using h
  constructor
  · intro n X
    have h := congrArg (fun f ↦ (S.ι X.stage).map f)
      (shiftFunctorAdd_zero_add_hom_app n X.obj)
    simpa [pbcPairShiftAdd, pbcPairShift, pbcPairShiftZero,
      Morphism.functor_map_ι, pbcStageShift, Functor.map_comp, eqToHom_map,
      Morphism.functor_obj] using h
  · intro n X
    have h := congrArg (fun f ↦ (S.ι X.stage).map f)
      (shiftFunctorAdd_add_zero_hom_app n X.obj)
    simpa [pbcPairShiftAdd, pbcPairShift, pbcPairShiftZero,
      pbcStageShift, Functor.map_comp, eqToHom_map,
      Morphism.functor_obj] using h

/-- The common-stage shift with the actual finite-stage unit and addition maps.
Source: blueprint common-stage calculus
(blueprint: prop-weil-pbc-common-stage-calculus). -/
def pbcPairShiftCore : ShiftMkCore S.PairCategory ℤ where
  F := pbcPairShift S
  zero := pbcPairShiftZero S
  add := pbcPairShiftAdd S
  assoc_hom_app := (pbcPairShift_laws S).1
  zero_add_hom_app := (pbcPairShift_laws S).2.1
  add_zero_hom_app := (pbcPairShift_laws S).2.2

/-- The canonical HasShift structure; its object action is (E,K) ↦ (E,K[n]).
Source: blueprint common-stage calculus
(blueprint: prop-weil-pbc-common-stage-calculus). -/
@[instance_reducible] def pbcPairHasShift : HasShift S.PairCategory ℤ :=
  hasShiftMk S.PairCategory ℤ (pbcPairShiftCore S)

attribute [instance] pbcPairHasShift

/-- The canonical comparison for the finite-stage inclusion is the inverse of the
upstream stage-morphism comparison. Source: blueprint common-stage calculus
(blueprint: prop-weil-pbc-common-stage-calculus). -/
def pbcStageInclusionShiftIso (i : I) (n : ℤ) :
    shiftFunctor (C i) n ⋙ S.ι i ≅ S.ι i ⋙ shiftFunctor S.PairCategory n :=
  ((pbcStageShift S n).ιCompFunctorIso i).symm

/-- The inclusion comparisons retain the zero and addition normalization of the stages.
Source: blueprint common-stage calculus
(blueprint: prop-weil-pbc-common-stage-calculus).
Proof: the comparison components for an included object are identities in the pair
category. Its compatibility with the zero and addition comparisons follows because
those were defined as the actual images of the same finite-stage comparisons. -/
theorem pbcStageInclusionShift_laws (i : I) :
    pbcStageInclusionShiftIso S i 0 = Functor.CommShift.isoZero (S.ι i) ℤ ∧
    ∀ n m : ℤ, pbcStageInclusionShiftIso S i (n + m) =
      Functor.CommShift.isoAdd (pbcStageInclusionShiftIso S i n)
        (pbcStageInclusionShiftIso S i m) := by
  constructor
  · ext X
    simp only [Functor.CommShift.isoZero_hom_app]
    rw [show shiftFunctorZero S.PairCategory ℤ = pbcPairShiftZero S from rfl]
    simp [pbcStageInclusionShiftIso, Morphism.ιCompFunctorIso,
      pbcPairShiftZero, ι_obj, Morphism.functor_obj, pbcStageShift, ← Functor.map_comp]
  · intro n m
    ext X
    simp only [Functor.CommShift.isoAdd_hom_app]
    rw [show shiftFunctorAdd S.PairCategory n m = pbcPairShiftAdd S n m from rfl]
    simp [pbcStageInclusionShiftIso, Morphism.ιCompFunctorIso,
      pbcPairShiftAdd, ι_obj, Morphism.functor_obj, pbcStageShift, ← Functor.map_comp]

/-- Finite-stage inclusions commute with the actual common-stage shift.
Source: blueprint common-stage calculus
(blueprint: prop-weil-pbc-common-stage-calculus). -/
instance pbcStageInclusionCommShift (i : I) : (S.ι i).CommShift ℤ where
  commShiftIso := pbcStageInclusionShiftIso S i
  commShiftIso_zero := (pbcStageInclusionShift_laws S i).1
  commShiftIso_add := (pbcStageInclusionShift_laws S i).2

section AdditiveShift
variable [stagePreadditive : ∀ i, Preadditive (C i)]
    [transitionAdditive : ∀ {i j : I} (h : i ≤ j), (S.T h).Additive]
    [stageShiftAdditive : ∀ i, ∀ n : ℤ, (shiftFunctor (C i) n).Additive]
include stagePreadditive transitionAdditive stageShiftAdditive

/-- The descended shift preserves the actual common-stage addition formula.
Source: blueprint common-stage calculus
(blueprint: prop-weil-pbc-common-stage-calculus).
Proof: represent two morphisms at a common stage. The stage shift is additive,
and pre- and post-composition by its comparison isomorphisms preserve sums.
The common-stage Hom quotient therefore identifies the shifted sum with the
sum of the shifted representatives. -/
theorem pbcPairShift_additive (n : ℤ) : (shiftFunctor S.PairCategory n).Additive := by
  have norm := (S.pairPreadditive_exists).exists.choose_spec
  constructor
  intro X Y f g
  obtain ⟨k, _, hX, hY, _, _, u, v, rfl, rfl⟩ :=
    PairCategory.exists_common_stage f g X.stage
  rw [← (norm X Y k hX hY u v).1]
  change (pbcStageShift S n).functor.map (PairCategory.mkHom k hX hY (u + v)) =
    (pbcStageShift S n).functor.map (PairCategory.mkHom k hX hY u) +
      (pbcStageShift S n).functor.map (PairCategory.mkHom k hX hY v)
  simp only [Morphism.functor_map_mkHom]
  dsimp only [Morphism.mapAt, pbcStageShift, Morphism.functor]
  simp only [Functor.map_add, Preadditive.comp_add, Preadditive.add_comp]
  exact (norm ((pbcPairShift S n).obj X) ((pbcPairShift S n).obj Y)
    k hX hY _ _).1

attribute [instance] pbcPairShift_additive

variable [∀ i, Limits.HasZeroObject (C i)]

/-- An included finite-stage zero object is a genuine zero object of the pair category.
Source: blueprint common-stage calculus
(blueprint: prop-weil-pbc-common-stage-calculus).
Proof: move a morphism from or to this object to any common stage. Additivity
of transition functors sends a zero object to a zero object, so its arrow is
uniquely zero there. The common-stage quotient preserves this equality. -/
theorem pbcPairZero_isZero (i : I) :
    Limits.IsZero ((S.ι i).obj (0 : C i)) := by
  apply (Limits.IsZero.iff_id_eq_zero _).mpr
  rw [← (S.ι i).map_id]
  change PairCategory.mkHom (X := ⟨i, (0 : C i)⟩)
    (Y := ⟨i, (0 : C i)⟩) i (le_refl i) (le_refl i)
      ((S.T (le_refl i)).map (𝟙 (0 : C i))) = 0
  have e : 𝟙 (0 : C i) = 0 := (Limits.isZero_zero (C i)).eq_zero_of_src _
  rw [e, Functor.map_zero]
  exact ((S.pairPreadditive_exists).exists.choose_spec _ _ i _ _ 0 0).2

/-- Existence of a zero object, witnessed by the image of any finite-stage zero.
Source: blueprint common-stage calculus
(blueprint: prop-weil-pbc-common-stage-calculus). -/
instance pbcPairHasZeroObject [Nonempty I] : Limits.HasZeroObject S.PairCategory :=
  (pbcPairZero_isZero S (Classical.choice (inferInstance : Nonempty I))).hasZeroObject

end AdditiveShift
end Shift

section FiniteDiagrams
variable [Nonempty I]

/-- Finite graphs of objects and arrows have simultaneous representatives.
Source: blueprint common-stage calculus (blueprint: prop-weil-pbc-common-stage-calculus).
Proof: choose one representative for each of the finitely many arrows. Directedness
provides one upper bound for their stages and for the finitely many object stages.
Transport every representative to that upper bound. The associator cocycle identifies
its quotient class with the original arrow. The empty graph uses any base stage. -/
theorem pbcFiniteGraph_representation {A B : Type w} [Finite A] [Finite B]
    (X : A → S.PairCategory) (s t : B → A)
    (f : ∀ b : B, X (s b) ⟶ X (t b)) :
    ∃ (M : I) (h : ∀ a : A, (X a).stage ≤ M)
      (u : ∀ b : B, (X (s b)).toStage (h (s b)) ⟶
        (X (t b)).toStage (h (t b))),
      ∀ b : B, PairCategory.mkHom M (h (s b)) (h (t b)) (u b) = f b := by
  classical
  choose k hX hY hk using fun b ↦ PairCategory.exists_mkHom_eq (f b)
  obtain ⟨M, hM⟩ := Finite.exists_le (fun q : A ⊕ B ↦
    Sum.elim (fun a ↦ (X a).stage) k q)
  let h : ∀ a : A, (X a).stage ≤ M := fun a ↦ hM (Sum.inl a)
  have hu : ∀ b : B, ∃ u : (X (s b)).toStage (h (s b)) ⟶
      (X (t b)).toStage (h (t b)),
      PairCategory.mkHom M (h (s b)) (h (t b)) u = f b := by
    intro b
    obtain ⟨u, e⟩ := hk b M (hM (Sum.inr b))
    exact ⟨u, e.symm⟩
  choose u hu using hu
  exact ⟨M, h, u, hu⟩

variable [∀ i, Preadditive (C i)]
    [∀ {i j : I} (h : i ≤ j), (S.T h).Additive]
    [∀ i, Limits.HasFiniteBiproducts (C i)]

/-- Finite direct sums descend without adjoining new objects.
Source: blueprint common-stage calculus (blueprint: prop-weil-pbc-common-stage-calculus).
Proof: transport the finitely many objects to one stage and take their biproduct
there. Include its injections and projections in the pair category. To test the
biproduct equations or its universal property, transport the finitely many arrows
to one further stage. Additive transitions preserve finite biproducts, so the
finite-stage equations give exactly the required pair-category equations. -/
@[instance] theorem pbcPairFiniteBiproducts : Limits.HasFiniteBiproducts S.PairCategory := by
  classical
  constructor
  intro n
  constructor
  intro X
  obtain ⟨M, h⟩ := Finite.exists_le (fun a : Fin n ↦ (X a).stage)
  have : (S.ι M).Additive := by
    constructor
    intro A B f g
    simp only [ι_map_eq (le_refl M), Functor.map_add]
    exact ((S.pairPreadditive_exists).exists.choose_spec _ _ M _ _ _ _).1
  let Y : Fin n → C M := fun a ↦ (X a).toStage (h a)
  have : Limits.HasProduct X := Limits.hasLimit_of_iso
    (F := Discrete.functor Y ⋙ S.ι M)
    (Discrete.natIso (fun a ↦ (S.isoToStage (X a.as) (h a.as)).symm))
  exact Limits.HasBiproduct.of_hasProduct X
end FiniteDiagrams

end CategoryTheory.StageSystem

namespace CategoryTheory.StageSystem

variable {I : Type w} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    {C : I → Type u} [∀ i, Category.{v} (C i)] (S : StageSystem C)
    [∀ i, Preadditive (C i)]
    [∀ {i j : I} (h : i ≤ j), (S.T h).Additive]
    [∀ i, HasShift (C i) ℤ]
    [∀ {i j : I} (h : i ≤ j), (S.T h).CommShift ℤ]
    [∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k),
      NatTrans.CommShift (S.assoc h h').hom ℤ]

/-- All finitely many asserted equalities are detected simultaneously at one
further stage. Source: blueprint order 1309
(blueprint: prop-weil-pbc-common-stage-calculus).
Proof: choose the eventual-equality witness for each equation and take an upper
bound of their finitely many stages and the prescribed starting stage. The
transport cocycle preserves each equality. Conversely the common stage witnesses
each quotient equality. The empty family only requires an upper bound of m. -/
theorem pbcFiniteEqualities_detection {A : Type c} [Finite A]
    (X Y : A → S.PairCategory)
    (r s : ∀ a : A, PairCategory.Rep (X a) (Y a)) (m : I) :
    (∀ a : A, PairCategory.mkHom (r a).k (r a).hX (r a).hY (r a).u =
      PairCategory.mkHom (s a).k (s a).hX (s a).hY (s a).u) ↔
    ∃ (N : I) (_ : m ≤ N) (hr : ∀ a : A, (r a).k ≤ N)
      (hs : ∀ a : A, (s a).k ≤ N),
      ∀ a : A, S.tr (hr a) (r a).u = S.tr (hs a) (s a).u := by
  classical
  constructor
  · intro e
    have he : ∀ a : A, ∃ (p : I) (hr : (r a).k ≤ p) (hs : (s a).k ≤ p),
        S.tr hr (r a).u = S.tr hs (s a).u :=
      fun a ↦ (PairCategory.mkHom_eq_mkHom_iff' _ _).mp (e a)
    choose p hr hs he using he
    obtain ⟨N, hN⟩ := Finite.exists_le (fun a : Option A ↦ a.elim m p)
    refine ⟨N, hN none, fun a ↦ (hr a).trans (hN (some a)),
      fun a ↦ (hs a).trans (hN (some a)), ?_⟩
    intro a
    exact PairCategory.Rep.rel_of_eq (hr a) (hs a) (he a) (hN (some a))
  · rintro ⟨N, _, hr, hs, e⟩ a
    exact (PairCategory.mkHom_eq_mkHom_iff' _ _).mpr ⟨N, hr a, hs a, e a⟩

/-- A literal clause-by-clause specification of the common-stage calculus, using
actual typed representatives, quotient morphisms and sigma comparisons.
Source: blueprint order 1309 (blueprint: prop-weil-pbc-common-stage-calculus). -/
structure CommonStageCalculusSpec : Prop where
  relation : ∀ X Y : S.PairCategory,
    _root_.Equivalence (PairCategory.Rep.Rel (X := X) (Y := Y))
  transport_add : ∀ {X Y : S.PairCategory} (r : PairCategory.Rep X Y)
    {N : I} (h : r.k ≤ N) (v : X.toStage r.hX ⟶ Y.toStage r.hY),
    S.tr h (r.u + v) = S.tr h r.u + S.tr h v
  transport_cocycle : ∀ {X Y : S.PairCategory} (r : PairCategory.Rep X Y)
    {N P : I} (h : r.k ≤ N) (k : N ≤ P),
    S.tr k (S.tr h r.u) = S.tr (h.trans k) r.u
  operations : S.PairPreadditiveNormalized (inferInstance : Preadditive S.PairCategory)
  negation : ∀ {X Y : S.PairCategory} (r : PairCategory.Rep X Y),
    -(PairCategory.mkHom r.k r.hX r.hY r.u) =
      PairCategory.mkHom r.k r.hX r.hY (-r.u)
  identity : ∀ X : S.PairCategory,
    𝟙 X = PairCategory.mkHom X.stage (le_refl _) (le_refl _) (𝟙 _)
  composition : ∀ {X Y Z : S.PairCategory}
    (r : PairCategory.Rep X Y) (s : PairCategory.Rep Y Z)
    (N : I) (hr : r.k ≤ N) (hs : s.k ≤ N),
    PairCategory.mkHom r.k r.hX r.hY r.u ≫ PairCategory.mkHom s.k s.hX s.hY s.u =
      PairCategory.mkHom N (r.hX.trans hr) (s.hY.trans hs) (S.tr hr r.u ≫ S.tr hs s.u)
  biproducts : Limits.HasFiniteBiproducts S.PairCategory
  finite_diagram : ∀ {A B : Type w} [Finite A] [Finite B]
    (X : A → S.PairCategory) (s t : B → A) (f : ∀ b : B, X (s b) ⟶ X (t b)),
    ∃ (M : I) (h : ∀ a : A, (X a).stage ≤ M)
      (u : ∀ b : B, (X (s b)).toStage (h (s b)) ⟶ (X (t b)).toStage (h (t b))),
      ∀ b : B, PairCategory.mkHom M (h (s b)) (h (t b)) (u b) = f b
  equalities : ∀ {A : Type w} [Finite A] (X Y : A → S.PairCategory)
    (r s : ∀ a : A, PairCategory.Rep (X a) (Y a)) (m : I),
    (∀ a : A, PairCategory.mkHom (r a).k (r a).hX (r a).hY (r a).u =
      PairCategory.mkHom (s a).k (s a).hX (s a).hY (s a).u) ↔
    ∃ (N : I) (_ : m ≤ N) (hr : ∀ a : A, (r a).k ≤ N)
      (hs : ∀ a : A, (s a).k ≤ N),
      ∀ a : A, S.tr (hr a) (r a).u = S.tr (hs a) (s a).u
  shift_objects : ∀ X : S.PairCategory,
    (shiftFunctor S.PairCategory (1 : ℤ)).obj X =
      ⟨X.stage, (shiftFunctor (C X.stage) (1 : ℤ)).obj X.obj⟩
  shift_maps : ∀ {X Y : S.PairCategory} (r : PairCategory.Rep X Y),
    (shiftFunctor S.PairCategory (1 : ℤ)).map
        (PairCategory.mkHom r.k r.hX r.hY r.u) =
      PairCategory.mkHom
        (X := (shiftFunctor S.PairCategory (1 : ℤ)).obj X)
        (Y := (shiftFunctor S.PairCategory (1 : ℤ)).obj Y) r.k r.hX r.hY
        (((S.T r.hX).commShiftIso (1 : ℤ)).hom.app X.obj ≫
          (shiftFunctor (C r.k) (1 : ℤ)).map r.u ≫
            ((S.T r.hY).commShiftIso (1 : ℤ)).inv.app Y.obj)
  shift_additive : (shiftFunctor S.PairCategory (1 : ℤ)).Additive
  inverse_additive : (shiftFunctor S.PairCategory (-1 : ℤ)).Additive
  inverse_left : Nonempty
    (shiftFunctor S.PairCategory (-1 : ℤ) ⋙ shiftFunctor S.PairCategory (1 : ℤ) ≅ 𝟭 _)
  inverse_right : Nonempty
    (shiftFunctor S.PairCategory (1 : ℤ) ⋙ shiftFunctor S.PairCategory (-1 : ℤ) ≅ 𝟭 _)
  inclusion_comparison : ∀ i : I, Nonempty ((S.ι i).CommShift ℤ)
  inclusion_normalization : ∀ (i : I) (n : ℤ),
    (S.ι i).commShiftIso n = pbcStageInclusionShiftIso S i n

private theorem commonStageCalculus_generic [∀ i, Limits.HasFiniteBiproducts (C i)]
    [∀ i, ∀ n : ℤ, (shiftFunctor (C i) n).Additive] :
    CommonStageCalculusSpec S := by
  have norm := (S.pairPreadditive_exists).exists.choose_spec
  refine {
    relation := fun X Y ↦ PairCategory.Rep.rel_equivalence
    transport_add := ?_
    transport_cocycle := fun {X Y} r {N P} h k ↦ tr_tr h k r.u
    operations := norm
    negation := ?_
    identity := fun X ↦ PairCategory.id_eq_mkHom X (le_refl _)
    composition := fun {X Y Z} r s N hr hs ↦ PairCategory.mkHom_comp_mkHom' r.u s.u hr hs
    biproducts := inferInstance
    finite_diagram := pbcFiniteGraph_representation S
    equalities := pbcFiniteEqualities_detection S
    shift_objects := fun X ↦ rfl
    shift_maps := fun {X Y} r ↦ rfl
    shift_additive := inferInstance
    inverse_additive := inferInstance
    inverse_left := ⟨shiftFunctorCompIsoId S.PairCategory (-1 : ℤ) 1 (by decide)⟩
    inverse_right := ⟨shiftFunctorCompIsoId S.PairCategory (1 : ℤ) (-1) (by decide)⟩
    inclusion_comparison := fun i ↦ ⟨inferInstance⟩
    inclusion_normalization := fun i n ↦ rfl }
  · intro X Y r N h v
    simp only [tr, Functor.map_add, Preadditive.comp_add, Preadditive.add_comp]
  · intro X Y r
    apply neg_eq_of_add_eq_zero_left
    rw [← (norm X Y r.k r.hX r.hY (-r.u) r.u).1, neg_add_cancel]
    exact (norm X Y r.k r.hX r.hY 0 0).2

end CategoryTheory.StageSystem

namespace AlgebraicGeometry.Scheme

open CategoryTheory.StageSystem

/-- Common-stage additive and shift calculus for the concrete finite coefficient
system of the node, with no arbitrary stage-category parameter.
Source: blueprint order 1309 (blueprint: prop-weil-pbc-common-stage-calculus).
Proof plan: (1) Integral finite sums and signed shifts preserve K-flatness,
completion and the normalized reduction towers. (2) The full integral categories
and their tensor-Hom rationalizations inherit the finite-stage additive structures.
(3) Expand associator-conjugated transport; the pentagon and naturality cancel
adjacent inverse associators, proving its cocycle and additivity. (4) Reflexivity
and symmetry are immediate; transitivity uses a compositum of the two witnesses.
(5) Move all representatives to one stage; cancellation proves compatibility of
composition, and additivity proves independence of sums and negatives. (6) The
included finite-stage zero and binary biproducts satisfy their five equations.
(7) The identity representatives give the isomorphisms to scalar-extended objects.
(8) Bound the finitely many arrow stages and equality witnesses simultaneously;
the empty diagram uses the base field. (9) Naturality of sigma and its associator
compatibility show that sigma-conjugated shift commutes with transport. (10) The
negative comparison is obtained by shifting the positive comparison inversely;
the adjacent sigma factors cancel in both inverse composites. Stage units give
the specified inclusion comparison.

Detailed proof from the DAG, including its dependency citations:

Step 1. We first supply the finite-stage additive and shift laws used below. In the ambient
derived category [def-weil-abstract-derived-category], binary direct sums are biproducts, and the
shift is the reindexing complex with negated differential. Tensoring module sheaves distributes
over a binary sum: the inverse maps are $(x,y)\otimes z\mapsto(x\otimes z,y\otimes z)$ and
$(x\otimes z,y\otimes w)\mapsto(x,0)\otimes z+(0,y)\otimes w$, first on sections and then on
sheafifications [def-pur-sheaf-tensor-product]. The total-tensor formula
[def-pc-tensor-complex-sheaves] gives the corresponding chain isomorphisms and commutation with
shifts: the identification $P[1]\otimes Q\to(P\otimes Q)[1]$ is the identity on reindexed
summands; for $P\otimes Q[1]\to(P\otimes Q)[1]$ multiply the summand of first-factor degree $p$ by
$(-1)^p$. In the latter formula the first differential changes the multiplier from $(-1)^p$ to
$(-1)^{p+1}$, and the second differential already has the negated differential of $Q$, giving
precisely the negative total differential. Reversing these identifications gives the
negative-shift formulas. By the definition of K-flatness, zero, finite sums and shifts of K-flat
complexes remain K-flat: tensoring an acyclic complex gives respectively zero, a finite sum of
acyclic complexes, or a shift of one [def-pc-kflat-complex]. Thus K-flat resolutions
[lem-pc-kflat-resolution] compute reductions and the Koszul towers
[def-weil-pbc-intrinsic-completion] of sums and shifts by sums and shifts of those of their
inputs. The coefficient-datum reduction functor [def-weil-pbc-adic-coefficient-datum] supplies the
natural reduction normalizations; the foregoing chain isomorphisms commute with the transition
maps $1\otimes q$.

Step 2. For the finite-stage category laws used below, use the full stated hypothesis that
$T_{F/E}:\mathcal C_E(T)\to\mathcal C_F(T)$ is an exact functor [prop-weil-pbc-scalar-extension],
not merely flatness of $F/E$. By [def-weil-triangulated-category], an exact functor is an additive
functor between pre-triangulated categories, whose categories are additive and whose shifts are
additive automorphisms. Apply this assertion with $F=E$, where $T_{E/E}=1$. It supplies the
finite-stage zero object, binary biproducts, Hom abelian groups, bilinear composition and inverse
shifts that this proof needs. Thus we use the stage structures included in the existing exactness
package; we do not independently assert that inverse image of an infinite completed-module limit
commutes with that limit on a refined stratum. The shift is the signed reindexing of
[def-weil-abstract-derived-category] on the full integral subcategory
[def-weil-pbc-bounded-constructible-complete] and the same objects in
[def-weil-pbc-rational-category]. It is $\mathcal O_E$-linear by its chain formula. The Hom
localization [def-weil-linear-scalar-localization] acts by $f\otimes a\mapsto f[1]\otimes a$, so
identities, composition, addition and the inverse shift descend. The biproduct maps satisfy their
five equations after tensoring with $1$. These explain the concrete finite-stage structures used
in the common-stage calculations without proving, or assuming, any identification with Stacks'
constant-coefficient category.

Step 3. For transport write $A_X=a_{N,M,E,K}$, $A_Y=a_{N,M,F,L}$, $B_X=a_{P,N,E,K}$,
$B_Y=a_{P,N,F,L}$, $C_X=a_{P,M,E,K}$, $C_Y=a_{P,M,F,L}$. Put $H=T_{N/M}$, $G=T_{P/N}$,
$J=T_{P/M}$, and $b=a_{P,N,M}:GH\xrightarrow{\sim}J$. The pentagon in
[prop-weil-pbc-scalar-extension] gives $B_XG(A_X)=C_Xb_{T_{M/E}K}$ and the analogous equation for
$Y$. Naturality of $b$ gives $b_YGH(u)=J(u)b_X$. Substituting in the transport formula of
[def-weil-pbc-finite-stage-pair-category] yields $$
(u_N)_P=B_YG(A_Y)GH(u)G(A_X)^{-1}B_X^{-1}=C_YJ(u)C_X^{-1}=u_P. $$ The unit equations give $u_M=u$.
Exact functors are additive by [def-weil-triangulated-category], so each $T_{N/M}$ is additive.
Distributivity of composition with fixed associators now gives $(u+v)_N=u_N+v_N$, $0_N=0$, and
$(-u)_N=-u_N$.

Step 4. Reflexivity has witness $M$ since $u_M=u$, and symmetry follows by reversing the equality.
If $(M,u)\sim(N,v)$ at $P_1$ and $(N,v)\sim(Q,w)$ at $P_2$, the finite compositum $P=P_1P_2$
exists by the directed-field data in [def-weil-pbc-finite-stage-pair-category]. Transporting both
equalities and using step 3 gives $u_P=v_P=w_P$, which witnesses transitivity. No injectivity of
the transport maps is assumed.

Step 5. For two composable arrows at $M$, the transported composite satisfies $$
v_Nu_N=a_ZT(v)a_Y^{-1}a_YT(u)a_X^{-1}=a_ZT(vu)a_X^{-1}=(vu)_N, $$ and transport of an identity is
an identity. If inputs are replaced by equivalent representatives, take the compositum of their
equality witnesses and the two proposed operation fields; by step 3 the corresponding inputs
coincide there. The displayed identity and additivity then make the outputs of addition, negation
and composition coincide there. Thus the operations in [def-weil-pbc-finite-stage-pair-category]
are independent of the field and representatives. All abelian-group, associativity, identity and
bilinearity equations are verified by putting their finitely many representatives over one stage
and applying the finite-stage laws established in step 2.

Step 6. There is also a zero object and every binary biproduct, as required by
[def-weil-additive-category]. Take $Z=(\Ql,0)$. Scalar extension sends the zero identity to the
zero identity, so every transport of $0$ is a zero object; every representative to or from $Z$ is
therefore zero. For $X=(E,K)$ and $Y=(F,L)$ choose $M\supseteq E,F$ and take $B=(M,T_{M/E}K\oplus
T_{M/F}L)$. Represent the four inclusions and projections at $M$ by the finite-stage ones. The
equations $p_ii_j=\delta_{ij}$ and $i_1p_1+i_2p_2=1$ hold at $M$, hence on classes by step 5; the
identity of $X$ is represented there by the identity of $T_{M/E}K$, and likewise for $Y$. These
prove that $B$ is a biproduct. Together with the Hom abelian groups and bilinear composition of
step 5, this makes $\mathcal P_T$ additive.

Step 7. For $X=(E,K)$ and $N\supseteq E$ construct $\gamma_{N,X}:X\to(N,T_{N/E}K)$ by the
representative $(N,1_{T_{N/E}K})$; the same identity represents a map in the opposite direction.
By the unit equations their composites are the two identity classes, so these maps are inverse.
For $f=[M,u]:X\to Y$ and $N\supseteq M$, all three maps in $\gamma_{N,Y}f\gamma_{N,X}^{-1}$ are
represented at $N$; the outer maps are identities and the middle map is $u_N$. Thus this conjugate
is $j_N(u_N)$. This constructs the object identifications mentioned but not defined in the
blueprint proof.

Step 8. For a finite diagram take the compositum of the coefficient fields of its objects and the
representative fields of its arrows, and use step 7 to replace every object by its isomorphic
scalar extension at this field. By step 5 all specified composites are represented by the
corresponding composites there. An asserted equality of parallel composites holds in $\mathcal
P_T$ if and only if its two representatives become equal at a further field, by the equivalence
relation in [def-weil-pbc-finite-stage-pair-category]. Take the compositum of the witnesses for
the finitely many asserted equalities. Step 3 preserves each witness equality at this common
field, giving all equations simultaneously. The reverse implication uses that field as a witness
for each equality. An empty diagram may use $\Ql$. If just the list of equalities is empty, no
witness extension is required: keep the field already containing the diagram's object and arrow
fields. Representation of objects is through the displayed isomorphisms, not literal equality of
pairs.

Step 9. Write $s_X=\sigma_{M/E,K}$, $s_Y=\sigma_{M/F,L}$, $h_X=\sigma_{N/M,T_{M/E}K}$,
$h_Y=\sigma_{N/M,T_{M/F}L}$, and let $A_X=a_{N,M,E,K}$ and $A'_X=a_{N,M,E,K[1]}$, with analogous
notation for $Y$. Associator compatibility of the natural shift comparisons
[prop-weil-pbc-scalar-extension] is $$ \sigma_{N/E,K}A'_X=A_X[1]h_XT_{N/M}(s_X). $$ Naturality
gives $h_YT_{N/M}(u[1])=(T_{N/M}u)[1]h_X$. Insert both identities and the transport formula into
$S_N(u_N)$, where $S_M(u)=s_Y^{-1}u[1]s_X$; the adjacent inverse comparisons cancel, leaving $$
S_N(u_N)=A'_YT_{N/M}(S_M(u))(A'_X)^{-1}. $$ Consequently equivalent representatives give
equivalent shifted representatives. At a common stage, $S_M(v)S_M(u)=S_M(vu)$ by cancellation of
the middle $s_Ys_Y^{-1}$, $S_M(1)=1$, and $S_M(u+v)=S_M(u)+S_M(v)$ by the additive finite-stage
shift of step 2. Thus the formula in the statement defines a well-defined additive endofunctor.

Step 10. Compute with the signed chain-reindexing shifts, for which $K[-1][1]=K=K[1][-1]$ and the
inverse identities on chain maps are literal [def-weil-abstract-derived-category]; in a choice
with inverse identifications, insert the corresponding natural unit and counit in these equations.
Write $q_{M/E,K}=(\sigma_{M/E,K[-1]})[-1]:(T_{M/E}K)[-1]\to T_{M/E}(K[-1])$ and
$\tau_{M/E,K}=q_{M/E,K}^{-1}$. Define $R_M(u)=\tau_{M/F,L}^{-1}u[-1]\tau_{M/E,K}$. For $H=T_{N/M}$
put $A_X=a_{N,M,E,K}$ and $A_X^-=a_{N,M,E,K[-1]}$, with analogous notation for $Y$. Apply $[-1]$
to the positive comparison equation of step 9 at $K[-1]$ and use naturality of the $H$ comparison
at $\sigma_{M/E,K[-1]}$. It reads $$q_{N/E,K}A_X[-1]=A_X^-H(q_{M/E,K})q_{N/M,T_{M/E}K}.$$
Multiplying by inverse $q$ factors gives
$$\tau_{N/E,K}A_X^-=A_X[-1]\tau_{N/M,T_{M/E}K}H(\tau_{M/E,K}).$$ Naturality gives
$\tau_{N/M,T_{M/F}L}H(u[-1])=(Hu)[-1]\tau_{N/M,T_{M/E}K}$. Substitution cancels the two middle
$\tau$ factors and yields $$R_N(u_N)=A_Y^-H(R_M(u))(A_X^-)^{-1}.$$ This is the equality required
for representative independence. At one stage the equations are explicitly
$R_M(v)R_M(u)=\tau_Z^{-1}v[-1]\tau_Y\tau_Y^{-1}u[-1]\tau_X=R_M(vu)$, $R_M(1)=\tau_X^{-1}\tau_X=1$,
and $R_M(u+v)=\tau_Y^{-1}(u[-1]+v[-1])\tau_X=R_M(u)+R_M(v)$; step 5 passes them to classes. For
the inverse composites put $s_X=\sigma_{M/E,K}$ and $t_X=\sigma_{M/E,K[-1]}$, and use the
corresponding $Y$ notation. Since $\tau_{M/E,K[1]}=(s_X[-1])^{-1}$ and $\tau_{M/E,K}[1]=t_X^{-1}$,
the two calculations are $$R_M(S_M(u))=s_Y[-1](s_Y[-1])^{-1}u\,s_X[-1](s_X[-1])^{-1}=u,$$
$$S_M(R_M(u))=t_Y^{-1}t_Y\,u\,t_X^{-1}t_X=u.$$ Represent the finite-stage inverse-shift unit and
counit at $E$ for $(E,K)$. The displayed equations prove their naturality at the representative
stage $M$ of every arrow, and their two triangle composites at a common stage are the identity
chain-reindexing maps. This gives an inverse equivalence $[-1]$. Finally $j_E(K)=(E,K)$ and
$j_E(u)=[E,u]$ preserve identities, composition and sums by step 5. With normalized identity
associators, the shift compatibility equation at $E= M=N$ is $\sigma_{E/E,K}=\sigma_{E/E,K}^2$.
Invertibility therefore gives $\sigma_{E/E,K}=1$. The formula at $M=E$ yields
$j_E(u)[1]=[E,u[1]]$, and the objects agree as well, giving the specified inclusion-shift
comparison. -/
theorem commonStageCalculus (l : ℕ) [Fact l.Prime] (Ω : Type c) [Field Ω]
    [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (T : Scheme.{u}) [IsNoetherian T]
    (hdim : ∃ m : ℕ, topologicalKrullDim T ≤ m)
    (hl : ∀ t : T, IsUnit (l : T.presheaf.stalk t)) :
    CommonStageCalculusSpec (pbcScalarSystem l Ω T hdim hl) := by
  exact commonStageCalculus_generic (pbcScalarSystem l Ω T hdim hl)

end AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
