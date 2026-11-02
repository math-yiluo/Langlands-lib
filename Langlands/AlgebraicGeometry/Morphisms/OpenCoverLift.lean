import Mathlib.AlgebraicGeometry.Gluing

/-! # Gluing factorizations through a scheme monomorphism -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- A morphism factors through a monomorphism `i` if it does so on every member of an open
cover of its source. -/
theorem exists_lift_of_openCover {X Y Y' : Scheme.{u}} (i : Y' ⟶ Y) [Mono i] (f : X ⟶ Y)
    (𝒰 : X.OpenCover) (h : ∀ k, ∃ g : 𝒰.X k ⟶ Y', g ≫ i = 𝒰.f k ≫ f) :
    ∃ f' : X ⟶ Y', f' ≫ i = f := by
  choose g hg using h
  refine ⟨Scheme.Cover.glueMorphisms 𝒰 g fun k l => ?_,
    Scheme.Cover.hom_ext 𝒰 _ _ fun k => ?_⟩
  · rw [← cancel_mono i, Category.assoc, Category.assoc, hg, hg, ← Category.assoc,
      pullback.condition, Category.assoc]
  · rw [Scheme.Cover.ι_glueMorphisms_assoc, hg]

end Langlands.AlgebraicGeometry
