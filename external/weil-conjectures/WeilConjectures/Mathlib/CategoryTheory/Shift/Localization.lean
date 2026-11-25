/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Shift.Localization
public import Mathlib.CategoryTheory.Shift.CommShiftTwo
public import Mathlib.CategoryTheory.Localization.Bifunctor

/-!
# Localization of bifunctors commuting with shifts

Let `L₁ : C₁ ⥤ D₁` and `L₂ : C₂ ⥤ D₂` be localization functors with respect to
`W₁ : MorphismProperty C₁` and `W₂ : MorphismProperty C₂` which commute with the shifts by `M`,
and let `G : D₁ ⥤ D₂ ⥤ E` be a bifunctor inducing `F : C₁ ⥤ C₂ ⥤ E` up to isomorphism
(`Localization.Lifting₂ L₁ L₂ W₁ W₂ F G`). If `F` commutes with the shifts in both variables
(`Functor.CommShift₂`), then so does `G` (`Functor.commShift₂OfLocalization`): this is the
two-variable analogue of `Functor.commShiftOfLocalization`.

The commutation isomorphisms `G.obj X₁ ⋙ shiftFunctor E m ≅ shiftFunctor D₂ m ⋙ G.obj X₁` are
defined uniformly in `X₁`, as the natural isomorphism of bifunctors
`Functor.CommShift₂OfLocalization.iso` induced by the corresponding natural isomorphism of
bifunctors for `F`. This is what makes them natural in `X₁`; at objects `X₁ = L₁.obj Y₁` they
agree with the structure given by `Functor.commShiftOfLocalization`.

We also show that two structures of commutation with the shifts on a functor out of a localized
category are equal if they both make a given isomorphism `L ⋙ F' ≅ G` compatible with the shifts
(`Functor.CommShift.eq_of_natTransCommShift`).

-/

@[expose] public section

namespace CategoryTheory

open Category Localization

section OneVariable

variable {C D E : Type*} [Category* C] [Category* D] [Category* E] (L : C ⥤ D)
  (W : MorphismProperty C) [L.IsLocalization W] {A : Type*} [AddMonoid A] [HasShift C A]
  [HasShift D A] [HasShift E A] [L.CommShift A]

include W in
/-- If two structures of commutation with the shifts on a functor `F'` out of a localized
category both make an isomorphism `L ⋙ F' ≅ G` commute with the shifts, then they are equal. -/
lemma Functor.CommShift.eq_of_natTransCommShift {F' : D ⥤ E} {G : C ⥤ E} [G.CommShift A]
    (S₁ S₂ : F'.CommShift A) (e : L ⋙ F' ≅ G)
    (h₁ : letI := S₁; NatTrans.CommShift e.hom A)
    (h₂ : letI := S₂; NatTrans.CommShift e.hom A) : S₁ = S₂ := by
  have key (a : A) : S₁.commShiftIso a = S₂.commShiftIso a := by
    ext1
    apply natTrans_ext L W
    intro X
    have e₁ := (letI := S₁; NatTrans.shift_app_comm e.hom a X)
    have e₂ := (letI := S₂; NatTrans.shift_app_comm e.hom a X)
    dsimp at e₁ e₂
    simp only [Functor.commShiftIso_comp_hom_app, assoc] at e₁ e₂
    rw [← cancel_epi (F'.map ((L.commShiftIso a).hom.app X)),
      ← cancel_mono ((e.hom.app X)⟦a⟧')]
    simpa only [assoc] using e₁.trans e₂.symm
  cases S₁
  cases S₂
  congr
  funext a
  exact key a

end OneVariable

variable {C₁ C₂ D₁ D₂ E : Type*} [Category* C₁] [Category* C₂] [Category* D₁] [Category* D₂]
  [Category* E] {M : Type*} [AddCommMonoid M]
  (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂) (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂)
  [L₁.IsLocalization W₁] [L₂.IsLocalization W₂] [W₁.ContainsIdentities] [W₂.ContainsIdentities]
  (F : C₁ ⥤ C₂ ⥤ E) (G : D₁ ⥤ D₂ ⥤ E) [Lifting₂ L₁ L₂ W₁ W₂ F G]

namespace Functor

namespace CommShift₂OfLocalization

section Obj

variable [HasShift C₂ M] [HasShift D₂ M] [HasShift E M] [L₂.CommShift M]
  [∀ X₁, (F.obj X₁).CommShift M]
  [∀ {X₁ Y₁ : C₁} (f : X₁ ⟶ Y₁), NatTrans.CommShift (F.map f) M]

/-- The commutation isomorphisms `F.obj X₁ ⋙ shiftFunctor E m ≅ shiftFunctor C₂ m ⋙ F.obj X₁`,
as a natural isomorphism of bifunctors. -/
@[simps!]
noncomputable def isoOfComponents (m : M) :
    F ⋙ (whiskeringLeft C₂ C₂ E).obj (shiftFunctor C₂ m) ≅
      F ⋙ (whiskeringRight C₂ E E).obj (shiftFunctor E m) :=
  NatIso.ofComponents (fun X₁ ↦ (F.obj X₁).commShiftIso m) (fun f ↦ by
    ext X₂
    exact (NatTrans.shift_app_comm (F.map f) m X₂).symm)

/-- The bifunctor `(X₁, X₂) ↦ G.obj X₁ (X₂⟦m⟧)` induces `(X₁, X₂) ↦ F.obj X₁ (X₂⟦m⟧)`. -/
@[instance_reducible]
noncomputable def liftingShift (m : M) :
    Lifting₂ L₁ L₂ W₁ W₂ (F ⋙ (whiskeringLeft C₂ C₂ E).obj (shiftFunctor C₂ m))
      (G ⋙ (whiskeringLeft D₂ D₂ E).obj (shiftFunctor D₂ m)) where
  iso := NatIso.ofComponents (fun X₁ ↦
    isoWhiskerRight (L₂.commShiftIso m).symm (G.obj (L₁.obj X₁)) ≪≫
      Functor.associator _ _ _ ≪≫
      isoWhiskerLeft (shiftFunctor C₂ m) ((Lifting₂.iso L₁ L₂ W₁ W₂ F G).app X₁)) (fun f ↦ by
    ext X₂
    have := congr_app ((Lifting₂.iso L₁ L₂ W₁ W₂ F G).hom.naturality f) (X₂⟦m⟧)
    dsimp at this ⊢
    simp only [id_comp]
    rw [assoc, ← this, NatTrans.naturality_assoc])

/-- The commutation isomorphisms `G.obj X₁ ⋙ shiftFunctor E m ≅ shiftFunctor D₂ m ⋙ G.obj X₁`,
as a natural isomorphism of bifunctors, induced by `isoOfComponents F m`. -/
noncomputable def iso (m : M) :
    G ⋙ (whiskeringLeft D₂ D₂ E).obj (shiftFunctor D₂ m) ≅
      G ⋙ (whiskeringRight D₂ E E).obj (shiftFunctor E m) :=
  letI := liftingShift L₁ L₂ W₁ W₂ F G m
  lift₂NatIso L₁ L₂ W₁ W₂ (F ⋙ (whiskeringLeft C₂ C₂ E).obj (shiftFunctor C₂ m))
    (F ⋙ (whiskeringRight C₂ E E).obj (shiftFunctor E m)) _ _ (isoOfComponents F m)

set_option backward.isDefEq.respectTransparency false in
omit [∀ X₁, (F.obj X₁).CommShift M]
  [∀ {X₁ Y₁ : C₁} (f : X₁ ⟶ Y₁), NatTrans.CommShift (F.map f) M] in
lemma iso_hom_app_app [∀ X₁, (F.obj X₁).CommShift M]
    [∀ {X₁ Y₁ : C₁} (f : X₁ ⟶ Y₁), NatTrans.CommShift (F.map f) M] (m : M) (Y₁ : C₁)
    (Y₂ : C₂) :
    ((iso L₁ L₂ W₁ W₂ F G m).hom.app (L₁.obj Y₁)).app (L₂.obj Y₂) =
      (G.obj (L₁.obj Y₁)).map ((L₂.commShiftIso m).inv.app Y₂) ≫
        ((Lifting₂.iso L₁ L₂ W₁ W₂ F G).hom.app Y₁).app (Y₂⟦m⟧) ≫
        ((F.obj Y₁).commShiftIso m).hom.app Y₂ ≫
        (((Lifting₂.iso L₁ L₂ W₁ W₂ F G).inv.app Y₁).app Y₂)⟦m⟧' := by
  simp [iso, liftingShift]
  rfl

/-- The functor `G.obj (L₁.obj Y₁)` is induced by `F.obj Y₁`. -/
@[instance_reducible]
noncomputable def liftingObj (Y₁ : C₁) : Lifting L₂ W₂ (F.obj Y₁) (G.obj (L₁.obj Y₁)) :=
  Lifting₂.fst L₁ L₂ W₁ W₂ F G Y₁

/-- At an object `L₁.obj Y₁`, the isomorphism `iso L₁ L₂ W₁ W₂ F G m` is the commutation
isomorphism of `Functor.commShiftOfLocalization` for `G.obj (L₁.obj Y₁)`. -/
lemma iso_app_eq (m : M) (Y₁ : C₁) :
    letI := liftingObj L₁ L₂ W₁ W₂ F G Y₁
    (iso L₁ L₂ W₁ W₂ F G m).app (L₁.obj Y₁) =
      commShiftOfLocalization.iso L₂ W₂ (F.obj Y₁) (G.obj (L₁.obj Y₁)) m := by
  let := liftingObj L₁ L₂ W₁ W₂ F G Y₁
  ext1
  apply natTrans_ext L₂ W₂
  intro Y₂
  rw [Iso.app_hom, iso_hom_app_app, commShiftOfLocalization.iso_hom_app]
  rfl

variable (M) in
/-- The commutation of `G.obj X₁` with the shifts, given by the natural isomorphism of
bifunctors `iso L₁ L₂ W₁ W₂ F G`. -/
@[instance_reducible]
noncomputable def commShiftObj (X₁ : D₁) : (G.obj X₁).CommShift M where
  commShiftIso m := (iso L₁ L₂ W₁ W₂ F G m).app X₁
  commShiftIso_zero := by
    have : iso L₁ L₂ W₁ W₂ F G 0 = NatIso.ofComponents
        (fun X₁ ↦ CommShift.isoZero (G.obj X₁) M) (fun f ↦ by
          ext X₂
          dsimp
          simp only [CommShift.isoZero_hom_app, assoc]
          rw [← NatTrans.naturality_assoc]
          congr 1
          simpa using ((shiftFunctorZero E M).inv.naturality ((G.map f).app X₂))) := by
      ext1
      apply natTrans₂_ext L₁ L₂ W₁ W₂
      intro Y₁ Y₂
      let := liftingObj L₁ L₂ W₁ W₂ F G Y₁
      have h := (commShiftOfLocalization L₂ W₂ M (F.obj Y₁) (G.obj (L₁.obj Y₁))).commShiftIso_zero
      exact (congr_app (congr_arg Iso.hom ((iso_app_eq L₁ L₂ W₁ W₂ F G 0 Y₁).trans h)) _ :)
    rw [this]
    rfl
  commShiftIso_add a b := by
    have : iso L₁ L₂ W₁ W₂ F G (a + b) = NatIso.ofComponents
        (fun X₁ ↦ CommShift.isoAdd ((iso L₁ L₂ W₁ W₂ F G a).app X₁)
          ((iso L₁ L₂ W₁ W₂ F G b).app X₁)) (fun f ↦ by
            ext X₂
            have ha := congr_app ((iso L₁ L₂ W₁ W₂ F G a).hom.naturality f) X₂
            have hb := congr_app ((iso L₁ L₂ W₁ W₂ F G b).hom.naturality f) (X₂⟦a⟧)
            dsimp at ha hb ⊢
            simp only [CommShift.isoAdd_hom_app, assoc, ← NatTrans.naturality_assoc, Iso.app_hom]
            congr 1
            simp only [Functor.comp_obj] at hb ⊢
            rw [reassoc_of% hb, ← Functor.map_comp_assoc, ha, Functor.map_comp, assoc]
            congr 2
            exact (shiftFunctorAdd E a b).inv.naturality ((G.map f).app X₂)) := by
      ext1
      apply natTrans₂_ext L₁ L₂ W₁ W₂
      intro Y₁ Y₂
      let := liftingObj L₁ L₂ W₁ W₂ F G Y₁
      have h :=
        (commShiftOfLocalization L₂ W₂ M (F.obj Y₁) (G.obj (L₁.obj Y₁))).commShiftIso_add a b
      have hab := (congr_app (congr_arg Iso.hom ((iso_app_eq L₁ L₂ W₁ W₂ F G (a + b) Y₁).trans h))
        (L₂.obj Y₂) :)
      let := commShiftOfLocalization L₂ W₂ M (F.obj Y₁) (G.obj (L₁.obj Y₁))
      have ea : (G.obj (L₁.obj Y₁)).commShiftIso a = (iso L₁ L₂ W₁ W₂ F G a).app (L₁.obj Y₁) :=
        (iso_app_eq L₁ L₂ W₁ W₂ F G a Y₁).symm
      have eb : (G.obj (L₁.obj Y₁)).commShiftIso b = (iso L₁ L₂ W₁ W₂ F G b).app (L₁.obj Y₁) :=
        (iso_app_eq L₁ L₂ W₁ W₂ F G b Y₁).symm
      rw [ea, eb] at hab
      exact hab
    rw [this]
    rfl

lemma commShiftObj_commShiftIso (X₁ : D₁) (m : M) :
    letI := commShiftObj M L₁ L₂ W₁ W₂ F G X₁
    (G.obj X₁).commShiftIso m = (iso L₁ L₂ W₁ W₂ F G m).app X₁ := rfl

lemma commShift_map {X₁ X₁' : D₁} (f : X₁ ⟶ X₁') :
    letI := commShiftObj M L₁ L₂ W₁ W₂ F G X₁
    letI := commShiftObj M L₁ L₂ W₁ W₂ F G X₁'
    NatTrans.CommShift (G.map f) M := by
  let := commShiftObj M L₁ L₂ W₁ W₂ F G X₁
  let := commShiftObj M L₁ L₂ W₁ W₂ F G X₁'
  refine ⟨fun m ↦ ?_⟩
  ext X₂
  exact (congr_app ((iso L₁ L₂ W₁ W₂ F G m).hom.naturality f) X₂).symm

/-- The component at `Y₁` of the isomorphism `Lifting₂.iso`, as a natural transformation
`L₂ ⋙ G.obj (L₁.obj Y₁) ⟶ F.obj Y₁`. -/
noncomputable def liftingIsoApp (Y₁ : C₁) : L₂ ⋙ G.obj (L₁.obj Y₁) ⟶ F.obj Y₁ :=
  (Lifting₂.iso L₁ L₂ W₁ W₂ F G).hom.app Y₁

lemma commShift_liftingIsoApp (Y₁ : C₁) :
    letI := commShiftObj M L₁ L₂ W₁ W₂ F G (L₁.obj Y₁)
    NatTrans.CommShift (liftingIsoApp L₁ L₂ W₁ W₂ F G Y₁) M := by
  let := commShiftObj M L₁ L₂ W₁ W₂ F G (L₁.obj Y₁)
  refine ⟨fun m ↦ ?_⟩
  ext Y₂
  dsimp [liftingIsoApp]
  simp only [commShiftIso_comp_hom_app, commShiftObj_commShiftIso, Iso.app_hom,
    iso_hom_app_app, assoc, ← Functor.map_comp_assoc, Functor.comp_obj,
    Functor.map_id, id_comp, ← Functor.map_comp, ← NatTrans.comp_app, Iso.inv_hom_id,
    Iso.hom_inv_id, NatTrans.id_app, comp_id]

end Obj

end CommShift₂OfLocalization

section

variable [HasShift C₁ M] [HasShift C₂ M] [HasShift D₁ M] [HasShift D₂ M] [HasShift E M]
  [L₁.CommShift M] [L₂.CommShift M] (h : CommShift₂Setup E M) [F.CommShift₂ h]

namespace CommShift₂OfLocalization

omit [HasShift C₁ M] [HasShift C₂ M] [HasShift D₁ M] [HasShift D₂ M] [HasShift E M]
  [L₁.CommShift M] [L₂.CommShift M] [F.CommShift₂ h] [L₁.IsLocalization W₁]
  [L₂.IsLocalization W₂] [W₁.ContainsIdentities] [W₂.ContainsIdentities] in
lemma liftingIso_flip_app_app (Y₁ : C₁) (Y₂ : C₂) :
    ((Lifting₂.iso L₂ L₁ W₂ W₁ F.flip G.flip).hom.app Y₂).app Y₁ =
      ((Lifting₂.iso L₁ L₂ W₁ W₂ F G).hom.app Y₁).app Y₂ := rfl

omit [HasShift C₁ M] [HasShift C₂ M] [HasShift D₁ M] [HasShift D₂ M] [HasShift E M]
  [L₁.CommShift M] [L₂.CommShift M] [F.CommShift₂ h] [L₁.IsLocalization W₁]
  [L₂.IsLocalization W₂] [W₁.ContainsIdentities] [W₂.ContainsIdentities] in
lemma liftingIso_flip_inv_app_app (Y₁ : C₁) (Y₂ : C₂) :
    ((Lifting₂.iso L₂ L₁ W₂ W₁ F.flip G.flip).inv.app Y₂).app Y₁ =
      ((Lifting₂.iso L₁ L₂ W₁ W₂ F G).inv.app Y₁).app Y₂ := rfl

lemma comm_aux_obj (Y₁ : C₁) (Y₂ : C₂) (m n : M) :
    ((iso L₁ L₂ W₁ W₂ F G n).hom.app ((L₁.obj Y₁)⟦m⟧)).app (L₂.obj Y₂) ≫
      (((iso L₂ L₁ W₂ W₁ F.flip G.flip m).hom.app (L₂.obj Y₂)).app (L₁.obj Y₁))⟦n⟧' =
    ((iso L₂ L₁ W₂ W₁ F.flip G.flip m).hom.app ((L₂.obj Y₂)⟦n⟧)).app (L₁.obj Y₁) ≫
      (((iso L₁ L₂ W₁ W₂ F G n).hom.app (L₁.obj Y₁)).app (L₂.obj Y₂))⟦m⟧' ≫
      (shiftComm ((G.obj (L₁.obj Y₁)).obj (L₂.obj Y₂)) m n).inv ≫ (h.ε m n).val.app _ := by
  have nα := congr_app ((iso L₁ L₂ W₁ W₂ F G n).hom.naturality
    ((L₁.commShiftIso m).hom.app Y₁)) (L₂.obj Y₂)
  have nβ := congr_app ((iso L₂ L₁ W₂ W₁ F.flip G.flip m).hom.naturality
    ((L₂.commShiftIso n).hom.app Y₂)) (L₁.obj Y₁)
  dsimp at nα nβ
  rw [← cancel_epi ((G.map ((L₁.commShiftIso m).hom.app Y₁)).app ((L₂.obj Y₂)⟦n⟧)), reassoc_of% nα]
  have nat := (G.map ((L₁.commShiftIso m).hom.app Y₁)).naturality
    ((L₂.commShiftIso n).hom.app Y₂)
  rw [← cancel_epi ((G.obj (L₁.obj (Y₁⟦m⟧))).map ((L₂.commShiftIso n).hom.app Y₂)),
    reassoc_of% nat, reassoc_of% nβ]
  simp only [iso_hom_app_app, liftingIso_flip_app_app, liftingIso_flip_inv_app_app,
    Functor.map_comp, assoc, Functor.flip_obj_map]
  simp only [← Functor.map_comp_assoc, ← NatTrans.comp_app, Iso.hom_inv_id,
    NatTrans.id_app, Functor.map_id, id_comp, ← Functor.map_comp, Functor.comp_obj]
  have hG (X₂ : D₂) : (G.map ((L₁.commShiftIso m).hom.app Y₁)).app X₂ ≫
      (G.map ((L₁.commShiftIso m).inv.app Y₁)).app X₂ = 𝟙 _ := by
    rw [← NatTrans.comp_app, ← G.map_comp, Iso.hom_inv_id_app, G.map_id, NatTrans.id_app]
  simp only [reassoc_of% hG, Iso.inv_hom_id_app_app_assoc, Functor.map_comp]
  congr 1
  rw [F.commShift₂_comm_assoc h Y₁ Y₂ m n]
  have h₁ := (shiftFunctorComm E m n).inv.naturality
    (((Lifting₂.iso L₁ L₂ W₁ W₂ F G).inv.app Y₁).app Y₂)
  have h₂ := (h.ε m n).val.naturality
    ((((Lifting₂.iso L₁ L₂ W₁ W₂ F G).inv.app Y₁).app Y₂)⟦m⟧'⟦n⟧')
  dsimp at h₁ h₂
  rw [← h₂]
  simp only [assoc]
  erw [reassoc_of% h₁]
  rfl

lemma comm_aux_naturality_left {X₁ X₁' : D₁} {X₂ X₂' : D₂} (f₁ : X₁ ⟶ X₁') (f₂ : X₂ ⟶ X₂')
    (m n : M) :
    (((iso L₁ L₂ W₁ W₂ F G n).hom.app (X₁⟦m⟧)).app X₂ ≫
      (((iso L₂ L₁ W₂ W₁ F.flip G.flip m).hom.app X₂).app X₁)⟦n⟧') ≫
      (((G.map f₁).app X₂ ≫ (G.obj X₁').map f₂)⟦m⟧')⟦n⟧' =
    ((G.map (f₁⟦m⟧')).app (X₂⟦n⟧) ≫ (G.obj (X₁'⟦m⟧)).map (f₂⟦n⟧')) ≫
      ((iso L₁ L₂ W₁ W₂ F G n).hom.app (X₁'⟦m⟧)).app X₂' ≫
      (((iso L₂ L₁ W₂ W₁ F.flip G.flip m).hom.app X₂').app X₁')⟦n⟧' := by
  have a₁ := congr_app ((iso L₁ L₂ W₁ W₂ F G n).hom.naturality (f₁⟦m⟧')) X₂
  have a₂ := ((iso L₁ L₂ W₁ W₂ F G n).hom.app (X₁'⟦m⟧)).naturality f₂
  have b₁ := ((iso L₂ L₁ W₂ W₁ F.flip G.flip m).hom.app X₂).naturality f₁
  have b₂ := congr_app ((iso L₂ L₁ W₂ W₁ F.flip G.flip m).hom.naturality f₂) X₁'
  dsimp at a₁ a₂ b₁ b₂
  simp only [assoc]
  rw [reassoc_of% a₂, reassoc_of% a₁]
  simp only [← Functor.map_comp, b₂, reassoc_of% b₁]

lemma comm_aux_naturality_right {X₁ X₁' : D₁} {X₂ X₂' : D₂} (f₁ : X₁ ⟶ X₁') (f₂ : X₂ ⟶ X₂')
    (m n : M) :
    (((iso L₂ L₁ W₂ W₁ F.flip G.flip m).hom.app (X₂⟦n⟧)).app X₁ ≫
      (((iso L₁ L₂ W₁ W₂ F G n).hom.app X₁).app X₂)⟦m⟧' ≫
      (shiftComm ((G.obj X₁).obj X₂) m n).inv ≫ (h.ε m n).val.app _) ≫
      (((G.map f₁).app X₂ ≫ (G.obj X₁').map f₂)⟦m⟧')⟦n⟧' =
    ((G.map (f₁⟦m⟧')).app (X₂⟦n⟧) ≫ (G.obj (X₁'⟦m⟧)).map (f₂⟦n⟧')) ≫
      ((iso L₂ L₁ W₂ W₁ F.flip G.flip m).hom.app (X₂'⟦n⟧)).app X₁' ≫
      (((iso L₁ L₂ W₁ W₂ F G n).hom.app X₁').app X₂')⟦m⟧' ≫
      (shiftComm ((G.obj X₁').obj X₂') m n).inv ≫ (h.ε m n).val.app _ := by
  have a₁ := congr_app ((iso L₁ L₂ W₁ W₂ F G n).hom.naturality f₁) X₂
  have a₂ := ((iso L₁ L₂ W₁ W₂ F G n).hom.app X₁').naturality f₂
  have b₁ := ((iso L₂ L₁ W₂ W₁ F.flip G.flip m).hom.app (X₂⟦n⟧)).naturality f₁
  have b₂ := congr_app ((iso L₂ L₁ W₂ W₁ F.flip G.flip m).hom.naturality (f₂⟦n⟧')) X₁'
  have c := (shiftFunctorComm E m n).inv.naturality ((G.map f₁).app X₂ ≫ (G.obj X₁').map f₂)
  have e := (h.ε m n).val.naturality
    ((((G.map f₁).app X₂ ≫ (G.obj X₁').map f₂)⟦m⟧')⟦n⟧')
  dsimp at a₁ a₂ b₁ b₂ c e
  simp only [assoc]
  rw [reassoc_of% b₂, reassoc_of% b₁, ← Functor.map_comp_assoc,
    ← Functor.map_comp_assoc]
  simp only [assoc]
  rw [a₂, reassoc_of% a₁, ← e]
  erw [← reassoc_of% c]
  simp only [Functor.map_comp, assoc]
  rfl

end CommShift₂OfLocalization

open CommShift₂OfLocalization in
/-- In the context of localization of categories, if a bifunctor is induced by a bifunctor
which commutes with the shifts in both variables, then it commutes with the shifts in both
variables. -/
@[instance_reducible]
noncomputable def commShift₂OfLocalization : G.CommShift₂ h where
  commShiftObj X₁ := commShiftObj M L₁ L₂ W₁ W₂ F G X₁
  commShift_map f := commShift_map L₁ L₂ W₁ W₂ F G f
  commShiftFlipObj X₂ := commShiftObj M L₂ L₁ W₂ W₁ F.flip G.flip X₂
  commShift_flip_map g := commShift_map L₂ L₁ W₂ W₁ F.flip G.flip g
  comm X₁ X₂ m n := by
    have := Localization.essSurj L₁ W₁
    have := Localization.essSurj L₂ W₂
    let e₁ := L₁.objObjPreimageIso X₁
    let e₂ := L₂.objObjPreimageIso X₂
    change ((iso L₁ L₂ W₁ W₂ F G n).hom.app (X₁⟦m⟧)).app X₂ ≫
      (((iso L₂ L₁ W₂ W₁ F.flip G.flip m).hom.app X₂).app X₁)⟦n⟧' =
      ((iso L₂ L₁ W₂ W₁ F.flip G.flip m).hom.app (X₂⟦n⟧)).app X₁ ≫
      (((iso L₁ L₂ W₁ W₂ F G n).hom.app X₁).app X₂)⟦m⟧' ≫
      (shiftComm ((G.obj X₁).obj X₂) m n).inv ≫ (h.ε m n).val.app _
    rw [← cancel_mono ((((G.map e₁.inv).app X₂ ≫ (G.obj _).map e₂.inv)⟦m⟧')⟦n⟧'),
      comm_aux_naturality_left, comm_aux_naturality_right, assoc, assoc,
      comm_aux_obj L₁ L₂ W₁ W₂ F G h]

end

end Functor

end CategoryTheory
