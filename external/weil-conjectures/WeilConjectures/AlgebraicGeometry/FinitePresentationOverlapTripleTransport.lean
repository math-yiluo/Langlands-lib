/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.LocalOverlapTransitions
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.ChosenPullback

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/--
Transport of a triple-overlap equation from one universal family of pullbacks to
any other family.  The proof uses the unique isomorphisms between chosen limits,
transition naturality, and cancellation by the pseudofunctor comparison
isomorphisms.  This is the universal-property step in the proof of the
persistent triple-overlap equation.
Source: Stacks Project, Tag 01ZR, first proof (Zariski gluing).
(blueprint: lem-pc-fp-overlap-triple-transport).
-/
theorem overlap_triple_transport
    {C : Type*} [Category C]
    {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat}
    {ι : Type*} {S : C} {X : ι → C} (g : ∀ a, X a ⟶ S)
    (T : F.OverlapTransitions g)
    (a b d : ι)
    (sq₀ : ∀ a b, ChosenPullback (g a) (g b))
    (sq₀₃ : ∀ a b d, ChosenPullback₃ (sq₀ a b) (sq₀ b d) (sq₀ a d))
    (h₀ :
      T.hom (sq₀₃ a b d).p (sq₀₃ a b d).p₁ (sq₀₃ a b d).p₂
          (sq₀₃ a b d).w₁ (sq₀₃ a b d).w₂ ≫
        T.hom (sq₀₃ a b d).p (sq₀₃ a b d).p₂ (sq₀₃ a b d).p₃
          (sq₀₃ a b d).w₂ (sq₀₃ a b d).w₃ =
      T.hom (sq₀₃ a b d).p (sq₀₃ a b d).p₁ (sq₀₃ a b d).p₃
          (sq₀₃ a b d).w₁ (sq₀₃ a b d).w₃)
    (sq : ∀ a b, ChosenPullback (g a) (g b))
    (sq₃ : ∀ a b d, ChosenPullback₃ (sq a b) (sq b d) (sq a d)) :
      T.hom (sq₃ a b d).p (sq₃ a b d).p₁ (sq₃ a b d).p₂
          (sq₃ a b d).w₁ (sq₃ a b d).w₂ ≫
        T.hom (sq₃ a b d).p (sq₃ a b d).p₂ (sq₃ a b d).p₃
          (sq₃ a b d).w₂ (sq₃ a b d).w₃ =
      T.hom (sq₃ a b d).p (sq₃ a b d).p₁ (sq₃ a b d).p₃
          (sq₃ a b d).w₁ (sq₃ a b d).w₃ := by
  obtain ⟨φ, hφ₁, hφ₂, hφ₃⟩ := (sq₀₃ a b d).exists_lift
    (sq₃ a b d).p₁ (sq₃ a b d).p₂ (sq₃ a b d).p₃ (sq₃ a b d).p
    (sq₃ a b d).w₁ (sq₃ a b d).w₂ (sq₃ a b d).w₃
  have hφ : φ ≫ (sq₀₃ a b d).p = (sq₃ a b d).p := by
    rw [← (sq₀₃ a b d).w₁, ← Category.assoc, hφ₁, (sq₃ a b d).w₁]
  rw [← T.pullHom_hom φ (sq₀₃ a b d).p (sq₃ a b d).p hφ
      (sq₀₃ a b d).p₁ (sq₀₃ a b d).p₂ (by simp) (by simp)
      (sq₃ a b d).p₁ (sq₃ a b d).p₂ hφ₁ hφ₂,
    ← T.pullHom_hom φ (sq₀₃ a b d).p (sq₃ a b d).p hφ
      (sq₀₃ a b d).p₂ (sq₀₃ a b d).p₃ (by simp) (by simp)
      (sq₃ a b d).p₂ (sq₃ a b d).p₃ hφ₂ hφ₃,
    ← T.pullHom_hom φ (sq₀₃ a b d).p (sq₃ a b d).p hφ
      (sq₀₃ a b d).p₁ (sq₀₃ a b d).p₃ (by simp) (by simp)
      (sq₃ a b d).p₁ (sq₃ a b d).p₃ hφ₁ hφ₃]
  dsimp [CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
  simp [← Functor.map_comp_assoc, h₀]

end AlgebraicGeometry
