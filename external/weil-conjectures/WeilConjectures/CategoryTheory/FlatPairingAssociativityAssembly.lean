/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Monoidal.Functor

/-! # Associativity of pairings from partial tensorator coherence -/

@[expose] public section

set_option autoImplicit false

universe uC uD vC vD

open CategoryTheory MonoidalCategory

namespace CategoryTheory

/-- Naturality and the canonical associator square imply associativity for arbitrary pairings.
Source: Stacks, Cohomology on Sites, Tag 06YU, functorial tensor coherence.
(auxiliary; not a blueprint node).
Proof: move the two pairing arrows through the tensorators using naturality. Apply the
canonical associator square to their common initial composite. Both remaining tails are
the images of the two sides of the given ordinary associativity equation. -/
theorem flatPairing_associativity_assembly
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [MonoidalCategory C] [MonoidalCategory D]
    (S : C ⥤ D) (P : C → Prop)
    (μ : ∀ L M : C, P L → (S.obj L ⊗ S.obj M ⟶ S.obj (L ⊗ M)))
    (A : ∀ L M N : C,
      (S.obj L ⊗ S.obj M) ⊗ S.obj N ⟶ S.obj L ⊗ (S.obj M ⊗ S.obj N))
    (h_tensor : ∀ {L M : C}, P L → P M → P (L ⊗ M))
    (h_natural : ∀ {L L' M M' : C} (f : L ⟶ L') (g : M ⟶ M')
      (hL : P L) (hL' : P L'),
      (S.map f ⊗ₘ S.map g) ≫ μ L' M' hL' = μ L M hL ≫ S.map (f ⊗ₘ g))
    (h_assoc : ∀ (L M N : C) (hL : P L) (hM : P M),
      μ L M hL ▷ S.obj N ≫ μ (L ⊗ M) N (h_tensor hL hM) ≫
          S.map (α_ L M N).hom =
        A L M N ≫ S.obj L ◁ μ M N hM ≫ μ L (M ⊗ N) hL)
    {L M N K Q R T : C} (hL : P L) (hM : P M) (hK : P K)
    (f : L ⊗ M ⟶ K) (g : K ⊗ N ⟶ R) (h : M ⊗ N ⟶ Q)
    (k : L ⊗ Q ⟶ T) (a : R ⟶ T)
    (w : f ▷ N ≫ g ≫ a = (α_ L M N).hom ≫ L ◁ h ≫ k) :
    (μ L M hL ≫ S.map f) ▷ S.obj N ≫
        (μ K N hK ≫ S.map g) ≫ S.map a =
      A L M N ≫ S.obj L ◁ (μ M N hM ≫ S.map h) ≫ (μ L Q hL ≫ S.map k) := by
  have nf := h_natural f (𝟙 N) (h_tensor hL hM) hK
  have nh := h_natural (𝟙 L) h hL hL
  simp only [Functor.map_id, tensorHom_id, id_tensorHom] at nf nh
  simp only [comp_whiskerRight, whiskerLeft_comp, Category.assoc]
  rw [reassoc_of% nf, reassoc_of% nh, ← reassoc_of% (h_assoc L M N hL hM)]
  simp only [← S.map_comp]
  rw [w]

end CategoryTheory
