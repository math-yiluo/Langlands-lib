/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Whiskering

/-! # Tower coherence descends from normalized representative squares

Source: Stacks 04VK; coefficient-comparison coherence in the blueprint.
(blueprint: lem-pur-functor-square-tower-descent). -/

@[expose] public section
set_option autoImplicit false
open CategoryTheory
namespace CategoryTheory

/-- Coherence of three normalized squares descends along a faithful restriction.
Source: Stacks 04VK, the localization universal property
(blueprint: lem-pur-functor-square-tower-descent).
Proof: restrict both routes to representatives. Precompose with the image of the
inverse first representative isomorphism and postcompose with the last two. Naturality
moves the first scalar representative map through the second square; its
normalization and the first normalization leave the representative tower square.
Use that square and naturality of the scalar associator, then the direct
normalization. Cancel the isomorphisms. Faithful restriction proves the equality
of transformations on the localized categories. -/
theorem functorSquareTowerDescent
    {R₀ R₁ R₂ D₀ D₁ D₂ C₀ C₁ C₂ : Type*}
    [Category R₀] [Category R₁] [Category R₂]
    [Category D₀] [Category D₁] [Category D₂]
    [Category C₀] [Category C₁] [Category C₂]
    (q₀ : R₀ ⥤ D₀) (q₁ : R₁ ⥤ D₁) (q₂ : R₂ ⥤ D₂)
    (k : R₀ ⥤ R₁) (h : R₁ ⥤ R₂) (m : R₀ ⥤ R₂) (κ : k ⋙ h ≅ m)
    (A : D₀ ⥤ D₁) (B : D₁ ⥤ D₂) (C : D₀ ⥤ D₂) (a : A ⋙ B ≅ C)
    (F : C₀ ⥤ C₁) (G : C₁ ⥤ C₂) (H : C₀ ⥤ C₂) (b : F ⋙ G ≅ H)
    (T₀ : D₀ ⥤ C₀) (T₁ : D₁ ⥤ C₁) (T₂ : D₂ ⥤ C₂)
    (t₀ : R₀ ⥤ C₀) (t₁ : R₁ ⥤ C₁) (t₂ : R₂ ⥤ C₂)
    (r₀ : q₀ ⋙ T₀ ≅ t₀) (r₁ : q₁ ⋙ T₁ ≅ t₁) (r₂ : q₂ ⋙ T₂ ≅ t₂)
    (η : q₀ ⋙ A ≅ k ⋙ q₁) (θ : q₁ ⋙ B ≅ h ⋙ q₂) (ζ : q₀ ⋙ C ≅ m ⋙ q₂)
    (c : ∀ P, F.obj (t₀.obj P) ⟶ t₁.obj (k.obj P))
    (d : ∀ P, G.obj (t₁.obj P) ⟶ t₂.obj (h.obj P))
    (e : ∀ P, H.obj (t₀.obj P) ⟶ t₂.obj (m.obj P))
    (α : T₀ ⋙ F ≅ A ⋙ T₁) (β : T₁ ⋙ G ≅ B ⋙ T₂) (γ : T₀ ⋙ H ≅ C ⋙ T₂)
    (ff : ((Functor.whiskeringLeft R₀ D₀ C₂).obj q₀).Faithful)
    (hα : ∀ P, F.map (r₀.hom.app P) ≫ c P =
      α.hom.app (q₀.obj P) ≫ T₁.map (η.hom.app P) ≫ r₁.hom.app (k.obj P))
    (hβ : ∀ P, G.map (r₁.hom.app P) ≫ d P =
      β.hom.app (q₁.obj P) ≫ T₂.map (θ.hom.app P) ≫ r₂.hom.app (h.obj P))
    (hγ : ∀ P, H.map (r₀.hom.app P) ≫ e P =
      γ.hom.app (q₀.obj P) ≫ T₂.map (ζ.hom.app P) ≫ r₂.hom.app (m.obj P))
    (hη : ∀ P, B.map (η.hom.app P) ≫ θ.hom.app (k.obj P) ≫ q₂.map (κ.hom.app P) =
      a.hom.app (q₀.obj P) ≫ ζ.hom.app P)
    (hc : ∀ P, G.map (c P) ≫ d (k.obj P) ≫ t₂.map (κ.hom.app P) =
      b.hom.app (t₀.obj P) ≫ e P) :
    ∀ K, G.map (α.hom.app K) ≫ β.hom.app (A.obj K) ≫ T₂.map (a.hom.app K) =
      b.hom.app (T₀.obj K) ≫ γ.hom.app K := by
  let lhs : T₀ ⋙ F ⋙ G ⟶ C ⋙ T₂ :=
    Functor.whiskerRight α.hom G ≫ Functor.whiskerLeft A β.hom ≫
      Functor.whiskerRight a.hom T₂
  let rhs : T₀ ⋙ F ⋙ G ⟶ C ⋙ T₂ := Functor.whiskerLeft T₀ b.hom ≫ γ.hom
  have heq : lhs = rhs := by
    let := ff
    apply ((Functor.whiskeringLeft R₀ D₀ C₂).obj q₀).map_injective
    apply NatTrans.ext
    funext P
    change G.map (α.hom.app (q₀.obj P)) ≫ β.hom.app (A.obj (q₀.obj P)) ≫
        T₂.map (a.hom.app (q₀.obj P)) =
      b.hom.app (T₀.obj (q₀.obj P)) ≫ γ.hom.app (q₀.obj P)
    apply (cancel_epi (G.map (F.map (r₀.inv.app P)))).mp
    apply (cancel_mono (T₂.map (ζ.hom.app P) ≫ r₂.hom.app (m.obj P))).mp
    have hn := β.hom.naturality (η.hom.app P)
    change G.map (T₁.map (η.hom.app P)) ≫ β.hom.app (q₁.obj (k.obj P)) =
      β.hom.app (A.obj (q₀.obj P)) ≫ T₂.map (B.map (η.hom.app P)) at hn
    have hr := r₂.hom.naturality (κ.hom.app P)
    change T₂.map (q₂.map (κ.hom.app P)) ≫ r₂.hom.app (m.obj P) =
      r₂.hom.app (h.obj (k.obj P)) ≫ t₂.map (κ.hom.app P) at hr
    have hb := b.hom.naturality (r₀.hom.app P)
    change G.map (F.map (r₀.hom.app P)) ≫ b.hom.app (t₀.obj P) =
      b.hom.app (T₀.obj (q₀.obj P)) ≫ H.map (r₀.hom.app P) at hb
    simp only [Category.assoc]
    rw [← T₂.map_comp_assoc, ← hη P, T₂.map_comp, T₂.map_comp]
    simp only [Category.assoc]
    rw [← reassoc_of% hn, hr, ← reassoc_of% (hβ (k.obj P))]
    have hhα := congrArg G.map (hα P)
    simp only [Functor.map_comp] at hhα
    rw [← reassoc_of% hhα]
    have hcancel : G.map (F.map (r₀.inv.app P)) ≫
        G.map (F.map (r₀.hom.app P)) = 𝟙 _ := by
      rw [← G.map_comp, ← F.map_comp, Iso.inv_hom_id_app, F.map_id, G.map_id]
    simp only [← Category.assoc]
    rw [hcancel, Category.id_comp]
    simp only [Category.assoc]
    rw [hc, ← hγ P, ← reassoc_of% hb]
    simp only [← Category.assoc]
    rw [hcancel, Category.id_comp]
  intro K
  exact congrArg (fun z ↦ z.app K) heq

end CategoryTheory
