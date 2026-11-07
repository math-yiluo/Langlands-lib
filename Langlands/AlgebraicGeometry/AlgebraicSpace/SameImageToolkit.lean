import Langlands.AlgebraicGeometry.AlgebraicSpace.SameImagePoints
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Basic properties of points with the same image -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : Presheaf S}

/-- Points of two schemes over `S` with the same image under maps to a presheaf. -/
def SameImage₂ {U V : Over S} (a : (schemeYoneda S).obj U ⟶ X) (b : (schemeYoneda S).obj V ⟶ X)
    (u : U.left) (v : V.left) : Prop :=
  ∃ (T : Over S) (g : T ⟶ U) (h : T ⟶ V) (t : T.left),
    (schemeYoneda S).map g ≫ a = (schemeYoneda S).map h ≫ b ∧ g.left t = u ∧ h.left t = v

theorem sameImage_iff {U : Over S} (a : (schemeYoneda S).obj U ⟶ X) (u u' : U.left) :
    SameImage a u u' ↔ SameImage₂ a a u u' :=
  Iff.rfl

theorem SameImage₂.refl {U : Over S} (a : (schemeYoneda S).obj U ⟶ X) (u : U.left) :
    SameImage₂ a a u u :=
  ⟨U, 𝟙 U, 𝟙 U, u, rfl, rfl, rfl⟩

theorem SameImage₂.symm {U V : Over S} {a : (schemeYoneda S).obj U ⟶ X}
    {b : (schemeYoneda S).obj V ⟶ X} {u : U.left} {v : V.left} (h : SameImage₂ a b u v) :
    SameImage₂ b a v u := by
  obtain ⟨T, g, h, t, e, hg, hh⟩ := h
  exact ⟨T, h, g, t, e.symm, hh, hg⟩

/-- The scheme pullback of two morphisms over `S`, as a scheme over `S`. -/
def overPullback {T₁ T₂ V : Over S} (h₁ : T₁ ⟶ V) (g₂ : T₂ ⟶ V) : Over S :=
  Over.mk (pullback.fst h₁.left g₂.left ≫ T₁.hom)

/-- The first projection of `overPullback`. -/
def overPullbackFst {T₁ T₂ V : Over S} (h₁ : T₁ ⟶ V) (g₂ : T₂ ⟶ V) :
    overPullback h₁ g₂ ⟶ T₁ :=
  Over.homMk (pullback.fst h₁.left g₂.left)

/-- The second projection of `overPullback`. -/
def overPullbackSnd {T₁ T₂ V : Over S} (h₁ : T₁ ⟶ V) (g₂ : T₂ ⟶ V) :
    overPullback h₁ g₂ ⟶ T₂ :=
  Over.homMk (pullback.snd h₁.left g₂.left) (by
    simp only [overPullback, Over.mk_hom]
    rw [← Over.w g₂, ← Category.assoc, ← pullback.condition, Category.assoc, Over.w h₁])

theorem overPullback_condition {T₁ T₂ V : Over S} (h₁ : T₁ ⟶ V) (g₂ : T₂ ⟶ V) :
    overPullbackFst h₁ g₂ ≫ h₁ = overPullbackSnd h₁ g₂ ≫ g₂ := by
  apply Over.OverMorphism.ext
  exact pullback.condition

theorem SameImage₂.trans {U V W : Over S} {a : (schemeYoneda S).obj U ⟶ X}
    {b : (schemeYoneda S).obj V ⟶ X} {c : (schemeYoneda S).obj W ⟶ X} {u : U.left}
    {v : V.left} {w : W.left} (h₁ : SameImage₂ a b u v) (h₂ : SameImage₂ b c v w) :
    SameImage₂ a c u w := by
  obtain ⟨T₁, g₁, k₁, t₁, e₁, hg₁, hk₁⟩ := h₁
  obtain ⟨T₂, g₂, k₂, t₂, e₂, hg₂, hk₂⟩ := h₂
  obtain ⟨t, ht₁, ht₂⟩ := Scheme.Pullback.exists_preimage_pullback t₁ t₂ (hk₁.trans hg₂.symm)
  refine ⟨overPullback k₁ g₂, overPullbackFst k₁ g₂ ≫ g₁, overPullbackSnd k₁ g₂ ≫ k₂, t,
    ?_, ?_, ?_⟩
  · rw [Functor.map_comp, Category.assoc, e₁, ← Category.assoc, ← Functor.map_comp,
      overPullback_condition, Functor.map_comp, Category.assoc, e₂, ← Category.assoc,
      ← Functor.map_comp]
  · simp only [Over.comp_left]
    change g₁.left (pullback.fst k₁.left g₂.left t) = u
    rw [ht₁, hg₁]
  · simp only [Over.comp_left]
    change k₂.left (pullback.snd k₁.left g₂.left t) = w
    rw [ht₂, hk₂]

theorem SameImage.refl {U : Over S} (a : (schemeYoneda S).obj U ⟶ X) (u : U.left) :
    SameImage a u u :=
  SameImage₂.refl a u

theorem SameImage.symm {U : Over S} {a : (schemeYoneda S).obj U ⟶ X} {u u' : U.left}
    (h : SameImage a u u') : SameImage a u' u :=
  SameImage₂.symm h

theorem SameImage.trans {U : Over S} {a : (schemeYoneda S).obj U ⟶ X} {u u' u'' : U.left}
    (h : SameImage a u u') (h' : SameImage a u' u'') : SameImage a u u'' :=
  SameImage₂.trans h h'

theorem sameImage_equivalence {U : Over S} (a : (schemeYoneda S).obj U ⟶ X) :
    Equivalence (SameImage a) :=
  ⟨SameImage.refl a, SameImage.symm, SameImage.trans⟩

/-- Composition with a morphism of schemes. -/
theorem SameImage₂.of_comp {U U' V : Over S} (φ : U' ⟶ U) {a : (schemeYoneda S).obj U ⟶ X}
    {b : (schemeYoneda S).obj V ⟶ X} {u : U'.left} {v : V.left}
    (h : SameImage₂ ((schemeYoneda S).map φ ≫ a) b u v) : SameImage₂ a b (φ.left u) v := by
  obtain ⟨T, g, k, t, e, hg, hk⟩ := h
  refine ⟨T, g ≫ φ, k, t, ?_, ?_, hk⟩
  · rw [Functor.map_comp, Category.assoc, e]
  · rw [Over.comp_left, Scheme.Hom.comp_apply, hg]

/-- A point of a scheme has the same image as its image under a morphism over the presheaf. -/
theorem SameImage₂.map {U U' : Over S} (φ : U' ⟶ U) (a : (schemeYoneda S).obj U ⟶ X)
    (u : U'.left) : SameImage₂ ((schemeYoneda S).map φ ≫ a) a u (φ.left u) :=
  ⟨U', 𝟙 U', φ, u, by simp, rfl, rfl⟩

theorem SameImage₂.of_comp_iff {U U' V : Over S} (φ : U' ⟶ U) {a : (schemeYoneda S).obj U ⟶ X}
    {b : (schemeYoneda S).obj V ⟶ X} (u : U'.left) (v : V.left) :
    SameImage₂ ((schemeYoneda S).map φ ≫ a) b u v ↔ SameImage₂ a b (φ.left u) v :=
  ⟨SameImage₂.of_comp φ, fun h => (SameImage₂.map φ a u).trans h⟩

/-- Points of a represented pullback realize every pair of points with the same image. -/
theorem SameImage₂.exists_pullback {U V : Over S} {a : (schemeYoneda S).obj U ⟶ X}
    {b : (schemeYoneda S).obj V ⟶ X} (hb : (schemeYoneda S).relativelyRepresentable b)
    {u : U.left} {v : V.left} (h : SameImage₂ a b u v) :
    ∃ p : (hb.pullback a).left, (hb.snd a).left p = u ∧ (hb.fst' a).left p = v := by
  obtain ⟨T, g, k, t, e, hg, hk⟩ := h
  have hl1 : hb.lift' k g e.symm ≫ hb.snd a = g := hb.lift'_snd k g e.symm
  have hl2 : hb.lift' k g e.symm ≫ hb.fst' a = k := hb.lift'_fst k g e.symm
  refine ⟨(hb.lift' k g e.symm).left t, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hl1, hg]
  · rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hl2, hk]

theorem SameImage₂.of_pullback {U V : Over S} {a : (schemeYoneda S).obj U ⟶ X}
    {b : (schemeYoneda S).obj V ⟶ X} (hb : (schemeYoneda S).relativelyRepresentable b)
    (p : (hb.pullback a).left) :
    SameImage₂ a b ((hb.snd a).left p) ((hb.fst' a).left p) :=
  ⟨hb.pullback a, hb.snd a, hb.fst' a, p, by
    rw [Functor.relativelyRepresentable.map_fst']
    exact ((hb.isPullback a).w).symm, rfl, rfl⟩

end Langlands.AlgebraicGeometry.AlgebraicSpace
