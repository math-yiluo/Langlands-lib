/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Compatible compositor squares

Source: Stacks Categories Tag 0B65; the elementary pasting calculation in the
internal/sectionwise module operation transport proof, Step 6.
(auxiliary; not a blueprint node)

Store both prescribed square isomorphisms and their component compatibility together.
-/

@[expose] public section

set_option autoImplicit false

universe uA vA uB vB uC vC uD vD

namespace CategoryTheory

private theorem paste_three
    {C : Type*} [Category C] {A B D E F G H : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : A ⟶ E) (d : E ⟶ F) (e : F ⟶ D)
    (x : B ⟶ G) (y : D ⟶ H) (z : G ⟶ H)
    {I J K : C} (k : G ⟶ I) (l : I ⟶ J) (m : J ⟶ K) (n : H ⟶ K)
    (h₁ : a ≫ b = c ≫ d ≫ e) (he : x ≫ z = b ≫ y)
    (h₂ : k ≫ l ≫ m = z ≫ n) :
    c ≫ d ≫ e ≫ y ≫ n = a ≫ x ≫ k ≫ l ≫ m := by
  rw [← reassoc_of% h₁, ← reassoc_of% he, ← h₂]

private theorem paste_natural_isos
    {C : Type uA} [Category.{vA} C] {D : Type uB} [Category.{vB} D]
    {E : Type uC} [Category.{vC} E] {B : Type uD} [Category.{vD} B]
    (F : D ⥤ E) (G : C ⥤ B)
    {FA FB FG FI : C ⥤ D} {FS FT FH FK : B ⥤ E}
    (a : FA ≅ FB) (x : FB ≅ FG) (k : FG ≅ FI)
    (e : FS ≅ FT) (y : FT ≅ FH) (n : FH ≅ FK)
    (M : C) {V W : E}
    (b : F.obj (FB.obj M) ⟶ FT.obj (G.obj M))
    (z : F.obj (FG.obj M) ⟶ FH.obj (G.obj M))
    (c : F.obj (FA.obj M) ⟶ V) (d : V ⟶ FS.obj (G.obj M))
    (l : F.obj (FI.obj M) ⟶ W) (m : W ⟶ FK.obj (G.obj M))
    (h₁ : F.map (a.hom.app M) ≫ b = c ≫ d ≫ e.hom.app (G.obj M))
    (he : F.map (x.hom.app M) ≫ z = b ≫ y.hom.app (G.obj M))
    (h₂ : F.map (k.hom.app M) ≫ l ≫ m = z ≫ n.hom.app (G.obj M)) :
    c ≫ d ≫ (e ≪≫ y ≪≫ n).hom.app (G.obj M) =
      F.map ((a ≪≫ x ≪≫ k).hom.app M) ≫ l ≫ m := by
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.map_comp, Category.assoc]
  exact paste_three _ _ _ _ _ _ _ _ _ _ _ _ h₁ he h₂

private theorem inverse_comparison
    {C : Type*} [Category C] {A B D E F : C}
    (a : A ≅ B) (b : A ⟶ D) (c : B ⟶ E) (d : E ⟶ F) (e : D ≅ F)
    (h : a.inv ≫ b = c ≫ d ≫ e.inv) : a.hom ≫ c ≫ d = b ≫ e.hom := by
  apply (cancel_epi a.inv).mp
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  rw [h]
  simp [Category.assoc]

private theorem inverse_natural_comparison
    {C : Type uA} [Category.{vA} C] {D : Type uB} [Category.{vB} D]
    {E : Type uC} [Category.{vC} E] {B : Type uD} [Category.{vD} B]
    (F : D ⥤ E) (G : C ⥤ B) {L R : C ⥤ D} {P Q : B ⥤ E}
    (a : L ≅ R) (e : P ≅ Q) (M : C) {V : E}
    (b : F.obj (L.obj M) ⟶ P.obj (G.obj M))
    (c : F.obj (R.obj M) ⟶ V) (d : V ⟶ Q.obj (G.obj M))
    (h : F.map (a.inv.app M) ≫ b = c ≫ d ≫ e.inv.app (G.obj M)) :
    F.map (a.hom.app M) ≫ c ≫ d = b ≫ e.hom.app (G.obj M) := by
  exact inverse_comparison (F.mapIso (a.app M)) b c d (e.app (G.obj M)) h

private theorem comparison_eq
    {I : Type*} {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    (E : A ⥤ C) (H : B ⥤ D) (F : I → A ⥤ B) (G : I → C ⥤ D)
    (c : ∀ i, F i ⋙ H ≅ E ⋙ G i) {i j : I} (w : i = j) (M : A) :
    H.map ((eqToIso (congrArg F w)).hom.app M) ≫ (c j).hom.app M =
      (c i).hom.app M ≫ (eqToIso (congrArg G w)).hom.app (E.obj M) := by
  subst j
  simp

/-- Pasting the two compositor comparisons and the comparison induced by an equality
of indices gives the comparison around the whole square.
Source: Stacks Categories Tag 0B65; node Step 6, elementary pasting calculation.
Proof: substitute the equality of indices for the middle comparison. Cancel the right
compositor in the second comparison and concatenate the three equalities, using
functoriality and associativity of composition.
(auxiliary; not a blueprint node) -/
theorem square_pasting
    {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    {I : Type*} (E : A ⥤ C) (H : B ⥤ D)
    (F : I → A ⥤ B) (G : I → C ⥤ D) (c : ∀ i, F i ⋙ H ≅ E ⋙ G i)
    {i j : I} (w : i = j) {L R : A ⥤ B} {Lb Rb : C ⥤ D}
    (a : L ≅ F i) (ab : Lb ≅ G i) (k : F j ≅ R) (kb : G j ≅ Rb)
    (M : A) {V W : D}
    (cl : H.obj (L.obj M) ⟶ V) (dl : V ⟶ Lb.obj (E.obj M))
    (cr : H.obj (R.obj M) ⟶ W) (dr : W ⟶ Rb.obj (E.obj M))
    (hl : H.map (a.hom.app M) ≫ (c i).hom.app M =
      cl ≫ dl ≫ ab.hom.app (E.obj M))
    (hr : H.map (k.inv.app M) ≫ (c j).hom.app M =
      cr ≫ dr ≫ kb.inv.app (E.obj M)) :
    cl ≫ dl ≫ (ab ≪≫ eqToIso (congrArg G w) ≪≫ kb).hom.app (E.obj M) =
      H.map ((a ≪≫ eqToIso (congrArg F w) ≪≫ k).hom.app M) ≫ cr ≫ dr := by
  have he := comparison_eq E H F G c w M
  have hr' := inverse_natural_comparison H E k kb M _ _ _ hr
  exact paste_natural_isos H E a (eqToIso (congrArg F w)) k
    ab (eqToIso (congrArg G w)) kb M _ _ _ _ _ _ hl he hr'

/-- The two composition-square isomorphisms and their component transport equation.
Source: Stacks Categories Tag 0B65; pasting the comparison squares in node Step 6.
(auxiliary; not a blueprint node) -/
structure CompatibleSquareComponents
    {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    (E : A ⥤ C) (H : B ⥤ D) (L R : A ⥤ B) (Lb Rb : C ⥤ D)
    (V W : A → D)
    (cl : ∀ M, H.obj (L.obj M) ⟶ V M) (dl : ∀ M, V M ⟶ Lb.obj (E.obj M))
    (cr : ∀ M, H.obj (R.obj M) ⟶ W M) (dr : ∀ M, W M ⟶ Rb.obj (E.obj M)) where
  internal : L ≅ R
  sectionwise : Lb ≅ Rb
  compatible (M : A) : cl M ≫ dl M ≫ sectionwise.hom.app (E.obj M) =
    H.map (internal.hom.app M) ≫ cr M ≫ dr M

/-- Construct compatible component squares by pasting the normalized comparisons.
Source: Stacks Categories Tag 0B65; the data are the given two compositors and the
isomorphism induced by the equality of composite scheme maps. Pasting the two
comparison equations and their inverses proves the compatibility field.
(auxiliary; not a blueprint node) -/
noncomputable def compatibleSquareComponents
    {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    {I : Type*} (E : A ⥤ C) (H : B ⥤ D)
    (F : I → A ⥤ B) (G : I → C ⥤ D) (c : ∀ i, F i ⋙ H ≅ E ⋙ G i)
    {i j : I} (w : i = j) {L R : A ⥤ B} {Lb Rb : C ⥤ D}
    (a : L ≅ F i) (ab : Lb ≅ G i) (k : F j ≅ R) (kb : G j ≅ Rb)
    (V W : A → D)
    (cl : ∀ M, H.obj (L.obj M) ⟶ V M) (dl : ∀ M, V M ⟶ Lb.obj (E.obj M))
    (cr : ∀ M, H.obj (R.obj M) ⟶ W M) (dr : ∀ M, W M ⟶ Rb.obj (E.obj M))
    (hl : ∀ M, H.map (a.hom.app M) ≫ (c i).hom.app M =
      cl M ≫ dl M ≫ ab.hom.app (E.obj M))
    (hr : ∀ M, H.map (k.inv.app M) ≫ (c j).hom.app M =
      cr M ≫ dr M ≫ kb.inv.app (E.obj M)) :
    CompatibleSquareComponents E H L R Lb Rb V W cl dl cr dr :=
  { internal := a ≪≫ eqToIso (congrArg F w) ≪≫ k
    sectionwise := ab ≪≫ eqToIso (congrArg G w) ≪≫ kb
    compatible := by
      intro M
      exact square_pasting E H F G c w a ab k kb M
        (cl M) (dl M) (cr M) (dr M) (hl M) (hr M) }

end CategoryTheory
