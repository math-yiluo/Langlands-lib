/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum

/-!
# Basic facts on descent data for schemes

We collect elementary facts on descent data in transport form
(`CategoryTheory.Over.DescentDatum`): the transport of a point only depends on the underlying
morphism, an effective descent datum is the one induced by the descended object, and morphisms
between effective descent data descend along fpqc coverings.
-/

@[expose] public section

universe v u

open CategoryTheory Limits

namespace CategoryTheory.Over.DescentDatum

section General

variable {C : Type u} [Category.{v} C] {X Y : C} {p : X ⟶ Y} {V : Over X}

/-- The transport of a point pulled back along `g` is the pullback along `g` of the transport,
in a form where the points are only matched through their underlying morphisms. -/
lemma transport_left_eq_comp (D : DescentDatum p V) {T T' : C} (g : T ⟶ T') (f₁ f₂ : T' ⟶ X)
    (h : f₁ ≫ p = f₂ ≫ p) (a' : Over.mk f₁ ⟶ V) {f₁' f₂' : T ⟶ X} (h' : f₁' ≫ p = f₂' ≫ p)
    (hf₁ : f₁' = g ≫ f₁) (hf₂ : f₂' = g ≫ f₂) (a : Over.mk f₁' ⟶ V) (ha : a.left = g ≫ a'.left) :
    (D.transport f₁' f₂' h' a).left = g ≫ (D.transport f₁ f₂ h a').left := by
  subst hf₁ hf₂
  obtain rfl : a = (Over.homMk g : Over.mk (g ≫ f₁) ⟶ Over.mk f₁) ≫ a' := by
    ext
    simp [ha]
  rw [D.transport_homMk_comp g f₁ f₂ h a']
  simp

/-- A form of `CategoryTheory.Over.DescentDatum.transport_left_congr` with the equations between
the morphisms oriented the other way. -/
lemma transport_left_congr' (D : DescentDatum p V) {T : C} {f₁ f₂ f₁' f₂' : T ⟶ X}
    (h : f₁ ≫ p = f₂ ≫ p) (h' : f₁' ≫ p = f₂' ≫ p) (hf₁ : f₁' = f₁) (hf₂ : f₂' = f₂)
    (a : Over.mk f₁ ⟶ V) (a' : Over.mk f₁' ⟶ V) (ha : a'.left = a.left) :
    (D.transport f₁' f₂' h' a').left = (D.transport f₁ f₂ h a).left :=
  D.transport_left_congr h' h a' a hf₁ hf₂ ha

/-- For an effective descent datum, with descended object `V₀` and projection `q`, the
transport of a point `a` over `f₁` is the unique point over `f₂` with the same image in `V₀`. -/
lemma transport_eq_of_isPullback (D : DescentDatum p V) {V₀ : Over Y} {q : V.left ⟶ V₀.left}
    (hq : IsPullback q V.hom V₀.hom p)
    (hD : ∀ {T : C} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ V),
      (D.transport f₁ f₂ h a).left ≫ q = a.left ≫ q)
    {T : C} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ V) (b : Over.mk f₂ ⟶ V)
    (hab : a.left ≫ q = b.left ≫ q) : D.transport f₁ f₂ h a = b := by
  ext
  refine hq.hom_ext ?_ ?_
  · rw [hD, hab]
  · rw [Over.w, Over.w b]

end General

end CategoryTheory.Over.DescentDatum

namespace CategoryTheory.Over.DescentDatum

open AlgebraicGeometry

variable {X Y : Scheme.{u}} {p : X ⟶ Y} {V : Over X}

/-- **Invariant morphisms descend.** Let `p : X ⟶ Y` be faithfully flat and quasi-compact and let
`D` be an effective descent datum on `V`, with descended scheme `V₀` and projection `q`. Then a
morphism `g : V ⟶ Z` which is invariant under the transport of `D` factors uniquely through `q`.
-/
lemma existsUnique_desc_of_isPullback [Flat p] [Surjective p] [QuasiCompact p]
    (D : DescentDatum p V) {V₀ : Over Y} {q : V.left ⟶ V₀.left}
    (hq : IsPullback q V.hom V₀.hom p)
    (hD : ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ V),
      (D.transport f₁ f₂ h a).left ≫ q = a.left ≫ q)
    {Z : Scheme.{u}} (g : V.left ⟶ Z)
    (hg : ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ V),
      (D.transport f₁ f₂ h a).left ≫ g = a.left ≫ g) :
    ∃! g₀ : V₀.left ⟶ Z, q ≫ g₀ = g := by
  have : Flat q := MorphismProperty.of_isPullback hq.flip inferInstance
  have : Surjective q := MorphismProperty.of_isPullback hq.flip inferInstance
  have : QuasiCompact q := MorphismProperty.of_isPullback hq.flip inferInstance
  have hw (T : Scheme.{u}) (g₁ g₂ : T ⟶ V.left) (h₁₂ : g₁ ≫ q = g₂ ≫ q) : g₁ ≫ g = g₂ ≫ g := by
    have hp : (g₁ ≫ V.hom) ≫ p = (g₂ ≫ V.hom) ≫ p := by
      rw [Category.assoc, Category.assoc, ← hq.w, reassoc_of% h₁₂]
    have := D.transport_eq_of_isPullback hq hD _ _ hp
      (Over.homMk (U := Over.mk (g₁ ≫ V.hom)) g₁ rfl)
      (Over.homMk (U := Over.mk (g₂ ≫ V.hom)) g₂ rfl) h₁₂
    have h' := hg _ _ hp (Over.homMk (U := Over.mk (g₁ ≫ V.hom)) g₁ rfl)
    rw [this] at h'
    exact h'.symm
  refine ⟨EffectiveEpi.desc q g (fun g₁ g₂ h ↦ hw _ g₁ g₂ h), EffectiveEpi.fac _ _ _,
    fun g₀ hg₀ ↦ ?_⟩
  rw [← cancel_epi q, hg₀, EffectiveEpi.fac]

end CategoryTheory.Over.DescentDatum

namespace CategoryTheory.Over

variable {C : Type u} [Category.{v} C] {X : C}

/-- The morphism `g : (S, g ≫ f) ⟶ (T, f)` of objects over `X`. -/
abbrev homMkComp {S T : C} {f : T ⟶ X} (g : S ⟶ T) : Over.mk (g ≫ f) ⟶ Over.mk f :=
  Over.homMk g

end CategoryTheory.Over
