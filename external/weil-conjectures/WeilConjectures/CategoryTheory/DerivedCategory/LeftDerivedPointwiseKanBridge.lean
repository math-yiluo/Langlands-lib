/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro

/-!
# Stacks-defined left derived values as pointwise Kan-extension values

Source: Stacks Project, Derived Categories, Tags 05S9 and 05SA, and Categories, Tags
05PU, 05Q4 and 002R (blueprint: lem-pur-left-derived-defined-pointwise-kan-bridge).
-/

@[expose] public section

universe u v uL vL uH vH

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

private noncomputable def denominatorToStructuredArrow
    {C : Type u} [Category.{v} C] {L : Type uL} [Category.{vL} L]
    (W : MorphismProperty C) (Q : C ⥤ L) [Q.IsLocalization W] (X : C) :
    W.Over ⊤ X ⥤ StructuredArrow (Q.obj X) Q where
  obj s := StructuredArrow.mk (Localization.isoOfHom Q W s.hom s.prop).inv
  map {s t} f := StructuredArrow.homMk f.left (by
    apply (cancel_mono (Localization.isoOfHom Q W t.hom t.prop).hom).mp
    simp only [Category.assoc, Localization.isoOfHom_hom, StructuredArrow.mk_hom_eq_self]
    rw [← Q.map_comp, MorphismProperty.Over.w f]
    simp only [Localization.isoOfHom_inv_hom_id]
    rfl)
  map_id s := by ext; rfl
  map_comp f g := by ext; rfl

private theorem fraction_leg_eq
    {C : Type u} [Category.{v} C] {L : Type uL} [Category.{vL} L]
    {H : Type uH} [Category.{vH} H]
    (W : MorphismProperty C) [W.HasRightCalculusOfFractions]
    (Q : C ⥤ L) [Q.IsLocalization W] (F : C ⥤ H) (X : C) (Y : H)
    (u : (Functor.const (W.Over ⊤ X)).obj Y ⟶
      MorphismProperty.Over.forget W ⊤ X ⋙ Over.forget X ⋙ F)
    {N : C} (a b : W.RightFraction X N)
    (h : a.map Q (Localization.inverts Q W) = b.map Q (Localization.inverts Q W)) :
    u.app (⟨Over.mk a.s, a.hs⟩ : W.Over ⊤ X) ≫ F.map a.f =
      u.app (⟨Over.mk b.s, b.hs⟩ : W.Over ⊤ X) ≫ F.map b.f := by
  obtain ⟨Z, t₁, t₂, hs, hf, ht⟩ :=
    (MorphismProperty.RightFraction.map_eq_iff Q W a b).mp h
  let k : W.Over ⊤ X := ⟨Over.mk (t₁ ≫ a.s), ht⟩
  let f₁ : k ⟶ (⟨Over.mk a.s, a.hs⟩ : W.Over ⊤ X) :=
    ⟨Over.homMk t₁, trivial, trivial⟩
  let f₂ : k ⟶ (⟨Over.mk b.s, b.hs⟩ : W.Over ⊤ X) :=
    ⟨Over.homMk t₂ hs.symm, trivial, trivial⟩
  have h₁ := u.naturality f₁
  have h₂ := u.naturality f₂
  dsimp at h₁ h₂
  simp only [Category.id_comp] at h₁ h₂
  change u.app (⟨Over.mk a.s, a.hs⟩ : W.Over ⊤ X) = u.app k ≫ F.map t₁ at h₁
  change u.app (⟨Over.mk b.s, b.hs⟩ : W.Over ⊤ X) = u.app k ≫ F.map t₂ at h₂
  rw [h₁, h₂, Category.assoc, Category.assoc, ← F.map_comp, ← F.map_comp, hf]

/-- An essentially constant denominator pro-diagram yields a pointwise right Kan limit,
with the supplied cone legs at inverse denominators and at the identity denominator.
Source: Stacks Project, Tags 05S9, 05SA and 05PU(2)
(blueprint: lem-pur-left-derived-defined-pointwise-kan-bridge).

The essential-constancy predicate records existence of a witnessing cone. The separately
quantified `u` and its retraction/factorization criterion specify any supplied witness,
so the conclusion preserves that witness rather than a privately chosen cone.

Proof:
1. Essential constancy (def-pc-essentially-constant-pro-diagram) makes the denominator cone
   a limit: for another cone `v` define its factorization by `v.app j₀ ≫ r`. Common-stage
   factorization gives every leg equation, and `u.app j₀ ≫ r = 𝟙 Y` gives uniqueness.
2. Represent each structured arrow by a right fraction (lem-pc-right-fraction-representation)
   and define its leg as the denominator leg followed by the image of the numerator.
   Common refinement (lem-pc-right-fraction-common-refinement) and naturality of `u`
   show independence of the representative and naturality of these legs.
3. Restrict any structured-arrow cone along the inverse-denominator functor and use the
   denominator limit of Step 1 for its lift. Every structured arrow receives a morphism
   from its representing inverse denominator, so naturality gives every leg equation.
   Restriction gives uniqueness. The identity numerator recovers each supplied `u_s`;
   the identity denominator gives the canonical comparison map of Definition 05S9. -/
theorem leftDerived_defined_pointwiseKan_bridge
    {C : Type u} [Category.{v} C] {L : Type uL} [Category.{vL} L]
    {H : Type uH} [Category.{vH} H]
    (W : MorphismProperty C) [W.HasRightCalculusOfFractions]
    (Q : C ⥤ L) [Q.IsLocalization W] (F : C ⥤ H) (X : C) (Y : H) :
    let G := MorphismProperty.Over.forget W ⊤ X ⋙ Over.forget X ⋙ F
    IsEssentiallyConstantProDiagram G Y →
      ∀ (u : (Functor.const (W.Over ⊤ X)).obj Y ⟶ G),
        (∃ (j₀ : W.Over ⊤ X) (r : G.obj j₀ ⟶ Y),
          u.app j₀ ≫ r = 𝟙 Y ∧
            ∀ j : W.Over ⊤ X, ∃ (k : W.Over ⊤ X) (a : k ⟶ j₀) (b : k ⟶ j),
              G.map b = G.map a ≫ r ≫ u.app j) →
        Q.HasPointwiseRightKanExtensionAt F (Q.obj X) ∧
          ∃ (π : (Functor.const (StructuredArrow (Q.obj X) Q)).obj Y ⟶
              StructuredArrow.proj (Q.obj X) Q ⋙ F),
            Nonempty (IsLimit (Cone.mk Y π)) ∧
              (∀ s : W.Over ⊤ X,
                π.app (StructuredArrow.mk (Localization.isoOfHom Q W s.hom s.prop).inv) =
                  u.app s) ∧
              ∀ h : W (𝟙 X),
                π.app (StructuredArrow.mk (𝟙 (Q.obj X))) =
                  u.app (⟨Over.mk (𝟙 X), h⟩ : W.Over ⊤ X) := by
  classical
  dsimp only
  intro _ u hu
  let G := MorphismProperty.Over.forget W ⊤ X ⋙ Over.forget X ⋙ F
  let z := fun j : StructuredArrow (Q.obj X) Q ↦
    (Localization.exists_rightFraction Q W j.hom).choose
  have hz (j : StructuredArrow (Q.obj X) Q) :
      (z j).map Q (Localization.inverts Q W) = j.hom :=
    (Localization.exists_rightFraction Q W j.hom).choose_spec.symm
  let leg := fun j : StructuredArrow (Q.obj X) Q ↦
    u.app (⟨Over.mk (z j).s, (z j).hs⟩ : W.Over ⊤ X) ≫ F.map (z j).f
  have hleg (j : StructuredArrow (Q.obj X) Q) (a : W.RightFraction X j.right)
      (ha : a.map Q (Localization.inverts Q W) = j.hom) :
      leg j = u.app (⟨Over.mk a.s, a.hs⟩ : W.Over ⊤ X) ≫ F.map a.f :=
    fraction_leg_eq W Q F X Y u (z j) a ((hz j).trans ha.symm)
  let π : (Functor.const (StructuredArrow (Q.obj X) Q)).obj Y ⟶
      StructuredArrow.proj (Q.obj X) Q ⋙ F :=
    { app := leg
      naturality := by
        intro i j f
        dsimp only [Functor.const_obj_map, Category.id_comp]
        let a : W.RightFraction X j.right :=
          .mk (z i).s (z i).hs ((z i).f ≫ f.right)
        have ha : a.map Q (Localization.inverts Q W) = j.hom := by
          change inv (Q.map (z i).s) ≫ Q.map ((z i).f ≫ f.right) = j.hom
          rw [Q.map_comp, ← Category.assoc]
          change (z i).map Q (Localization.inverts Q W) ≫ Q.map f.right = j.hom
          rw [hz i, StructuredArrow.w f]
        rw [hleg j a ha]
        dsimp [leg, a]
        simp only [Functor.map_comp, Category.assoc, Category.id_comp] }
  have hden (s : W.Over ⊤ X) :
      π.app (StructuredArrow.mk (Localization.isoOfHom Q W s.hom s.prop).inv) =
        u.app s := by
    change leg (StructuredArrow.mk
      (Localization.isoOfHom Q W s.hom s.prop).inv) = u.app s
    rw [hleg _ (MorphismProperty.RightFraction.ofInv s.hom s.prop) (by
      simp [MorphismProperty.RightFraction.map, MorphismProperty.RightFraction.ofInv,
        Localization.isoOfHom])]
    cases s with
    | mk s hs =>
      cases s with
      | mk l r h =>
        cases r
        change u.app (⟨Over.mk h, hs⟩ : W.Over ⊤ X) ≫ F.map (𝟙 l) = _
        erw [F.map_id, Category.comp_id]
        congr 1
  obtain ⟨j₀, r, hr, hfactor⟩ := hu
  let c : Cone G := Cone.mk Y u
  have hc : IsLimit c :=
    { lift := fun v ↦ v.π.app j₀ ≫ r
      fac := by
        intro v j
        obtain ⟨k, a, b, hab⟩ := hfactor j
        calc
          (v.π.app j₀ ≫ r) ≫ u.app j =
              (v.π.app k ≫ G.map a) ≫ r ≫ u.app j := by rw [v.w a, Category.assoc]
          _ = v.π.app k ≫ G.map b := by rw [Category.assoc, ← hab]
          _ = v.π.app j := v.w b
      uniq := by
        intro v m hm
        calc
          m = m ≫ (u.app j₀ ≫ r) := by rw [hr, Category.comp_id]
          _ = v.π.app j₀ ≫ r := by rw [← Category.assoc, hm j₀] }
  let d : Cone (StructuredArrow.proj (Q.obj X) Q ⋙ F) := Cone.mk Y π
  let I := denominatorToStructuredArrow W Q X
  have hd : IsLimit d :=
    { lift := fun v ↦ hc.lift (v.whisker I)
      fac := by
        intro v j
        let a := z j
        let s : W.Over ⊤ X := ⟨Over.mk a.s, a.hs⟩
        let f : I.obj s ⟶ j := StructuredArrow.homMk a.f (hz j)
        change hc.lift (v.whisker I) ≫ leg j = v.π.app j
        rw [hleg j a (hz j), ← Category.assoc]
        change (hc.lift (v.whisker I) ≫ c.π.app s) ≫ F.map a.f = v.π.app j
        rw [hc.fac (v.whisker I) s]
        exact v.w f
      uniq := by
        intro v m hm
        apply hc.uniq (v.whisker I) m
        intro s
        change m ≫ u.app s = v.π.app (I.obj s)
        rw [← hden s]
        exact hm (I.obj s) }
  exact ⟨⟨⟨d, hd⟩⟩, π, ⟨hd⟩, hden, fun h ↦ by
    have hh := hden (⟨Over.mk (𝟙 X), h⟩ : W.Over ⊤ X)
    change π.app (StructuredArrow.mk (Localization.isoOfHom Q W (𝟙 X) h).inv) = _ at hh
    rw [Localization.isoOfHom_id_inv] at hh
    exact hh⟩

end CategoryTheory
