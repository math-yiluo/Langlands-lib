/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Equivalence

@[expose] public section

open CategoryTheory
namespace AlgebraicGeometry

/-- Inverting a five-isomorphism triangle and cancelling its final edge.
The inverse of the forward triangle reverses the factors; composing with
the final isomorphism cancels its inverse. -/
theorem iso_triangle_inverse_cancel
    {C : Type*} [Category* C] {A B D E F : C}
    (a : A ≅ B) (b : B ≅ F) (c : A ≅ D) (d : D ≅ E) (e : E ≅ F)
    (h : a.hom ≫ b.hom = c.hom ≫ d.hom ≫ e.hom) :
    e.hom ≫ b.inv ≫ a.inv = d.inv ≫ c.inv := by
  have hi : b.inv ≫ a.inv = e.inv ≫ d.inv ≫ c.inv := by
    have h' := (Iso.inv_eq_inv (a ≪≫ b) (c ≪≫ d ≪≫ e)).2 (by
      simpa only [Iso.trans_hom, Category.assoc] using h)
    simpa only [Iso.trans_inv, Category.assoc] using h'
  rw [hi]
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- The component of a comparison obtained by cancelling an equivalence
pair is its counit component followed by the remaining comparison. -/
theorem counit_comparison_component
    {A B C D : Type*} [Category* A] [Category* B]
    [Category* C] [Category* D]
    (R : A ⥤ B) (I : B ⥤ C) (F : C ⥤ B) (P : B ⥤ D) (Q : A ⥤ D)
    (η : I ⋙ F ≅ 𝟭 B)
    (α : R ⋙ P ≅ Q)
    (X : A) :
    (Functor.associator R I (F ⋙ P) ≪≫
      Functor.isoWhiskerLeft R (Functor.associator I F P).symm ≪≫
      Functor.isoWhiskerLeft R (Functor.isoWhiskerRight η P) ≪≫
      Functor.isoWhiskerLeft R (Functor.leftUnitor P) ≪≫ α).hom.app X =
      P.map (η.hom.app (R.obj X)) ≫ α.hom.app X := by
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.leftUnitor_hom_app, Functor.comp_obj, Functor.id_obj,
    Category.id_comp]

/-- The inverse associator followed by right whiskering has the mapped
component of the original natural isomorphism. -/
theorem associator_symm_whiskerRight_hom_app
    {A B C D : Type*} [Category* A] [Category* B]
    [Category* C] [Category* D]
    (F : A ⥤ B) (G : B ⥤ C) (H : C ⥤ D) (J : A ⥤ C)
    (α : F ⋙ G ≅ J) (X : A) :
    ((Functor.associator F G H).symm ≪≫
      Functor.isoWhiskerRight α H).hom.app X =
        H.map (α.hom.app X) := by
  simp only [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
    Functor.associator_inv_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.comp_obj, Category.id_comp]

/-- A return unit followed by an equivalence counit cancels across any comparison.
Proof: The triangle identity identifies the image of the inverse unit with
the counit on the image object. Naturality moves that counit across the
comparison isomorphism, whose inverse then cancels. -/
theorem equivalence_return_cancel
    {C D : Type*} [Category* C] [Category* D]
    (e : C ≌ D) (M : C) (N : D) (α : N ≅ e.functor.obj M) :
    e.functor.map (e.inverse.map α.hom) ≫
      e.functor.map (e.unitIso.inv.app M) ≫
        e.functor.map (𝟙 M) ≫ α.inv = e.counitIso.hom.app N := by
  have hε : e.functor.map (e.unitIso.inv.app M) =
      e.counitIso.hom.app (e.functor.obj M) := by
    apply (cancel_epi (e.functor.map (e.unitIso.hom.app M))).1
    calc
      e.functor.map (e.unitIso.hom.app M) ≫
          e.functor.map (e.unitIso.inv.app M) = 𝟙 _ := by
        rw [← e.functor.map_comp, Iso.hom_inv_id_app, e.functor.map_id]
      _ = e.functor.map (e.unitIso.hom.app M) ≫
          e.counitIso.hom.app (e.functor.obj M) :=
        (e.functor_unitIso_comp M).symm
  have hn := e.counitIso.hom.naturality α.hom
  simp only [Functor.comp_map, Functor.id_map] at hn
  have hId : e.functor.map (𝟙 M) = 𝟙 (e.functor.obj M) := e.functor.map_id M
  rw [hε, hId]
  have hdrop :
      (e.functor.map (e.inverse.map α.hom) ≫
        e.counitIso.hom.app (e.functor.obj M)) ≫ 𝟙 (e.functor.obj M) =
        e.functor.map (e.inverse.map α.hom) ≫
          e.counitIso.hom.app (e.functor.obj M) := Category.comp_id _
  simp only [← Category.assoc]
  rw [hdrop, hn]
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Paste a two-step return triangle with its terminal cancellation.
The proof is associativity followed by the two supplied equations. -/
theorem paste_return_triangle
    {C : Type*} [Category* C] {A B D E F G : C}
    {a : A ⟶ B} {b : B ⟶ D} {c : D ⟶ G}
    {p : A ⟶ E} {q : E ⟶ F} {r : F ⟶ D} {s : F ⟶ G}
    (htriangle : a ≫ b = p ≫ q ≫ r) (hcancel : r ≫ c = s) :
    a ≫ b ≫ c = p ≫ q ≫ s := by
  calc
    a ≫ b ≫ c = (a ≫ b) ≫ c := (Category.assoc a b c).symm
    _ = (p ≫ q ≫ r) ≫ c := congrArg (fun z ↦ z ≫ c) htriangle
    _ = p ≫ q ≫ (r ≫ c) := by simp only [Category.assoc]
    _ = p ≫ q ≫ s := by rw [hcancel]

/-- Paste a three-map middle cancellation into a surrounding two-map prefix
and one-map suffix. Associativity gives the displayed factorization, and the
two supplied equations replace its middle and then its whole composite. -/
theorem paste_middle_three
    {C₀ : Type*} [Category* C₀]
    {A B C D E F G : C₀}
    {a : A ⟶ B} {b : B ⟶ C} {c : C ⟶ D}
    {d : D ⟶ E} {e : E ⟶ F} {f : F ⟶ G}
    {x : C ⟶ F} {y : A ⟶ G}
    (hmiddle : c ≫ d ≫ e = x)
    (houter : a ≫ b ≫ x ≫ f = y) :
    a ≫ b ≫ c ≫ d ≫ e ≫ f = y := by
  calc
    a ≫ b ≫ c ≫ d ≫ e ≫ f = (a ≫ b) ≫ (c ≫ d ≫ e) ≫ f := by
      simp only [Category.assoc]
    _ = a ≫ b ≫ x ≫ f := by rw [hmiddle]; simp only [Category.assoc]
    _ = y := houter

/-- Insert a six-map comparison between fixed prefix and suffix morphisms.
The proof only reassociates composition and substitutes the supplied middle
equation; no categorical structure beyond associativity is used. -/
theorem paste_six_with_edges
    {C₀ : Type*} [Category* C₀]
    {A B C D E F G H I J : C₀}
    {p : A ⟶ B} {a : B ⟶ C} {b : C ⟶ D} {c : D ⟶ E}
    {d : E ⟶ F} {e : F ⟶ G} {f : G ⟶ H}
    {x : B ⟶ I} {y : I ⟶ H} {q : H ⟶ J}
    (hmiddle : a ≫ b ≫ c ≫ d ≫ e ≫ f = x ≫ y) :
    p ≫ a ≫ b ≫ c ≫ d ≫ e ≫ f ≫ q = p ≫ x ≫ y ≫ q := by
  calc
    p ≫ a ≫ b ≫ c ≫ d ≫ e ≫ f ≫ q =
        p ≫ (a ≫ b ≫ c ≫ d ≫ e ≫ f) ≫ q := by simp only [Category.assoc]
    _ = p ≫ (x ≫ y) ≫ q := by rw [hmiddle]
    _ = p ≫ x ≫ y ≫ q := by simp only [Category.assoc]

/-- An equivalence counit is invariant under transport to an isomorphic object.
Proof: Naturality of the counit moves the isomorphism through the counit;
its inverse then cancels. This is the object-level cancellation for nested
open restrictions after the first return triangle. -/
theorem equivalence_counit_transport_cancel
    {C D : Type*} [Category* C] [Category* D]
    (e : C ≌ D) {X Y : D} (α : X ≅ Y) :
    e.functor.map (e.inverse.map α.hom) ≫ e.counitIso.hom.app Y ≫ α.inv =
      e.counitIso.hom.app X := by
  have hn := e.counitIso.hom.naturality α.hom
  simp only [Functor.comp_map, Functor.id_map] at hn
  rw [← Category.assoc, hn]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- A natural comparison followed by an equivalence counit ignores transport
along an isomorphism of its input. Proof: naturality moves the input map
through the comparison, and counit naturality moves it back; the inverse
input map then cancels. This is the local-object cancellation in either
canonical overlap branch. -/
theorem equivalence_comparison_counit_transport
    {A C D E : Type*} [Category* A] [Category* C] [Category* D] [Category* E]
    (e : C ≌ D) (cart : D ⥤ E) (H : A ⥤ C) (S : A ⥤ D)
    (ω : H ≅ S ⋙ e.inverse) {a b : A} (φ : a ≅ b) :
    let apex := e.functor ⋙ cart
    apex.map (H.map φ.hom) ≫ apex.map (ω.hom.app b) ≫
        cart.map (e.counitIso.hom.app (S.obj b)) ≫ cart.map (S.map φ.inv) =
      apex.map (ω.hom.app a) ≫ cart.map (e.counitIso.hom.app (S.obj a)) := by
  intro apex
  have hω := ω.hom.naturality φ.hom
  simp only [Functor.comp_map] at hω
  have hε := equivalence_counit_transport_cancel e (S.mapIso φ)
  simp only [Functor.mapIso_hom, Functor.mapIso_inv] at hε
  calc
    apex.map (H.map φ.hom) ≫ apex.map (ω.hom.app b) ≫
        cart.map (e.counitIso.hom.app (S.obj b)) ≫ cart.map (S.map φ.inv) =
      apex.map (H.map φ.hom ≫ ω.hom.app b) ≫
        cart.map (e.counitIso.hom.app (S.obj b)) ≫ cart.map (S.map φ.inv) := by
          simp only [Functor.map_comp, Category.assoc]
    _ = apex.map (ω.hom.app a ≫ e.inverse.map (S.map φ.hom)) ≫
        cart.map (e.counitIso.hom.app (S.obj b)) ≫ cart.map (S.map φ.inv) := by
          rw [hω]
    _ = apex.map (ω.hom.app a) ≫ cart.map
          (e.functor.map (e.inverse.map (S.map φ.hom))) ≫
            cart.map (e.counitIso.hom.app (S.obj b)) ≫ cart.map (S.map φ.inv) := by
          dsimp only [apex, Functor.comp_map]
          simp only [Functor.map_comp, Category.assoc]
    _ = apex.map (ω.hom.app a) ≫ cart.map (e.counitIso.hom.app (S.obj a)) := by
          simp only [← Functor.map_comp]
          rw [hε]

end AlgebraicGeometry
