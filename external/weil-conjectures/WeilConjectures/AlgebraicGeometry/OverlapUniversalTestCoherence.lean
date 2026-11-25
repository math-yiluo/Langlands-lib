/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.LocalOverlapTransitions
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.ChosenPullback

/-! # Coherence from universal overlap tests

Source: Stacks Project, Tag 01ZR, first proof.
(blueprint: lem-pc-overlap-universal-test-coherence). -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Raw transition coherence follows from diagonal and universal triple tests.
Source: Stacks Project, Tag 01ZR, first proof, Zariski gluing.
(blueprint: lem-pc-overlap-universal-test-coherence).

Proof: Pull each tested diagonal identity along an arbitrary chart map. For an
arbitrary triple of chart maps with common image in the base, the universal
property of the chosen threefold pullback supplies their common lift. Pull the
tested triple equation along that lift. Naturality identifies all three pulled
maps with the supplied transition maps. The pseudofunctor comparison isomorphisms
cancel and its pullback functor preserves identity and composition. -/
theorem coherent_of_universal_tests {C : Type*} [Category C]
    {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat}
    {ι : Type*} {S : C} {X : ι → C} {f : ∀ a, X a ⟶ S}
    (T : F.OverlapTransitions f)
    (sq : ∀ a b, Limits.ChosenPullback (f a) (f b))
    (sq₃ : ∀ a b c, Limits.ChosenPullback₃ (sq a b) (sq b c) (sq a c))
    (hself : ∀ a, T.hom (f a) (𝟙 _) (𝟙 _) (Category.id_comp _)
      (Category.id_comp _) = 𝟙 _)
    (hcomp : ∀ a b c,
      T.hom (sq₃ a b c).p (sq₃ a b c).p₁ (sq₃ a b c).p₂
        (sq₃ a b c).w₁ (sq₃ a b c).w₂ ≫
      T.hom (sq₃ a b c).p (sq₃ a b c).p₂ (sq₃ a b c).p₃
        (sq₃ a b c).w₂ (sq₃ a b c).w₃ =
      T.hom (sq₃ a b c).p (sq₃ a b c).p₁ (sq₃ a b c).p₃
        (sq₃ a b c).w₁ (sq₃ a b c).w₃) :
    T.Coherent where
  hom_self Y q a g hg := by
    have h := T.pullHom_hom g (f a) q hg (𝟙 _) (𝟙 _) (by simp) (by simp)
      g g (by simp) (by simp)
    rw [hself] at h
    simpa [CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom] using h.symm
  hom_comp Y q a b c f₁ f₂ f₃ hf₁ hf₂ hf₃ := by
    obtain ⟨φ, hφ₁, hφ₂, hφ₃⟩ := (sq₃ a b c).exists_lift f₁ f₂ f₃ q hf₁ hf₂ hf₃
    have hφ : φ ≫ (sq₃ a b c).p = q := by
      rw [← (sq₃ a b c).w₁, ← Category.assoc, hφ₁, hf₁]
    rw [← T.pullHom_hom φ (sq₃ a b c).p q hφ (sq₃ a b c).p₁
        (sq₃ a b c).p₂ (by simp) (by simp) f₁ f₂ hφ₁ hφ₂,
      ← T.pullHom_hom φ (sq₃ a b c).p q hφ (sq₃ a b c).p₂
        (sq₃ a b c).p₃ (by simp) (by simp) f₂ f₃ hφ₂ hφ₃,
      ← T.pullHom_hom φ (sq₃ a b c).p q hφ (sq₃ a b c).p₁
        (sq₃ a b c).p₃ (by simp) (by simp) f₁ f₃ hφ₁ hφ₃]
    dsimp [CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
    simp [← Functor.map_comp_assoc, hcomp]
end AlgebraicGeometry
