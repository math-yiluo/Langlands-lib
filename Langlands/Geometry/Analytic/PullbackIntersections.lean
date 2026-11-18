import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Intersections of test objects over a pullback -/

noncomputable section

universe u v

open CategoryTheory

namespace Langlands.Analytic.SpaceAnalytification

/-- Intersecting the two pairwise relations over the base recovers the
relation over a categorical pullback. -/
theorem isPullback_intersection_of_isPullback
    {C : Type u} [Category.{v} C]
    {W X₁ X₂ Z A B C₀ C₁ C₂ D : C}
    {π₁ : W ⟶ X₁} {π₂ : W ⟶ X₂} {f₁ : X₁ ⟶ Z} {f₂ : X₂ ⟶ Z}
    (hw : IsPullback π₁ π₂ f₁ f₂) (x : A ⟶ W) (y : B ⟶ W)
    {a₀ : C₀ ⟶ A} {b₀ : C₀ ⟶ B}
    {a₁ : C₁ ⟶ A} {b₁ : C₁ ⟶ B} {a₂ : C₂ ⟶ A} {b₂ : C₂ ⟶ B}
    (h₀ : IsPullback a₀ b₀ (x ≫ π₁ ≫ f₁) (y ≫ π₁ ≫ f₁))
    (h₁ : IsPullback a₁ b₁ (x ≫ π₁) (y ≫ π₁))
    (h₂ : IsPullback a₂ b₂ (x ≫ π₂) (y ≫ π₂))
    (u₁ : C₁ ⟶ C₀) (u₂ : C₂ ⟶ C₀)
    (hu₁a : u₁ ≫ a₀ = a₁) (hu₁b : u₁ ≫ b₀ = b₁)
    (hu₂a : u₂ ≫ a₀ = a₂) (hu₂b : u₂ ≫ b₀ = b₂)
    {d₁ : D ⟶ C₁} {d₂ : D ⟶ C₂} (hd : IsPullback d₁ d₂ u₁ u₂) :
    IsPullback (d₁ ≫ a₁) (d₁ ≫ b₁) x y := by
  have ha : d₁ ≫ a₁ = d₂ ≫ a₂ := by
    calc
      d₁ ≫ a₁ = (d₁ ≫ u₁) ≫ a₀ := by rw [Category.assoc, hu₁a]
      _ = (d₂ ≫ u₂) ≫ a₀ := by rw [hd.w]
      _ = d₂ ≫ a₂ := by rw [Category.assoc, hu₂a]
  have hb : d₁ ≫ b₁ = d₂ ≫ b₂ := by
    calc
      d₁ ≫ b₁ = (d₁ ≫ u₁) ≫ b₀ := by rw [Category.assoc, hu₁b]
      _ = (d₂ ≫ u₂) ≫ b₀ := by rw [hd.w]
      _ = d₂ ≫ b₂ := by rw [Category.assoc, hu₂b]
  have hcomm : (d₁ ≫ a₁) ≫ x = (d₁ ≫ b₁) ≫ y := by
    apply hw.hom_ext
    · simpa only [Category.assoc] using congrArg (fun k => d₁ ≫ k) h₁.w
    · rw [ha, hb]
      simpa only [Category.assoc] using congrArg (fun k => d₂ ≫ k) h₂.w
  apply IsPullback.mk' hcomm
  · intro T l m hl hm
    apply hd.hom_ext
    · apply h₁.hom_ext
      · simpa only [Category.assoc] using hl
      · simpa only [Category.assoc] using hm
    · apply h₂.hom_ext
      · simpa only [← ha, Category.assoc] using hl
      · simpa only [← hb, Category.assoc] using hm
  · intro T a b hab
    obtain ⟨l₁, hl₁a, hl₁b⟩ := h₁.exists_lift a b
      (by simpa only [Category.assoc] using congrArg (fun k => k ≫ π₁) hab)
    obtain ⟨l₂, hl₂a, hl₂b⟩ := h₂.exists_lift a b
      (by simpa only [Category.assoc] using congrArg (fun k => k ≫ π₂) hab)
    have hl : l₁ ≫ u₁ = l₂ ≫ u₂ := by
      apply h₀.hom_ext
      · rw [Category.assoc, Category.assoc, hu₁a, hu₂a, hl₁a, hl₂a]
      · rw [Category.assoc, Category.assoc, hu₁b, hu₂b, hl₁b, hl₂b]
    obtain ⟨l, hld₁, -⟩ := hd.exists_lift l₁ l₂ hl
    exact ⟨l, by rw [← Category.assoc, hld₁, hl₁a],
      by rw [← Category.assoc, hld₁, hl₁b]⟩

end Langlands.Analytic.SpaceAnalytification
