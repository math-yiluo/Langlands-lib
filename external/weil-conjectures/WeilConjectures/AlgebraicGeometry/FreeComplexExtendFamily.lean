/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-! Recursive extension of a comparison map along an exact resolution.
Source: literature/stacks-project/algebra.tex, Tag 00LS.
(blueprint: lem-weil-pbc-free-complex-extend-family).
-/

@[expose] public section

universe u

open CategoryTheory

/-- Given the degree-zero lift, projectivity and exactness recursively produce
all higher components of the chain map.  The theorem packages the dependent
infinite recursion from Tag 00LS into one strictly lower intermediate claim.
Source: Algebra, Tag 00LS, proof of lemma-compare-resolutions (1), lines 17527--17535.
(blueprint: lem-weil-pbc-free-complex-extend-family). -/
theorem free_complex_extend_family
    (R : Type u) [CommRing R]
    (N : ModuleCat R) (N' : ℕ → ModuleCat R)
    (d : ∀ i : ℕ, N' (i + 1) ⟶ N' i)
    (η : N' 0 ⟶ N)
    (hd0 : d 0 ≫ η = 0)
    (hd : ∀ i : ℕ, d (i + 1) ≫ d i = 0)
    (hex0 : (ShortComplex.mk (d 0) η hd0).Exact)
    (hex : ∀ i : ℕ, (ShortComplex.mk (d (i + 1)) (d i) (hd i)).Exact)
    (F : ℕ → ModuleCat R)
    (δ : ∀ i : ℕ, F (i + 1) ⟶ F i)
    (hδ : ∀ i : ℕ, δ (i + 1) ≫ δ i = 0)
    (hfree : ∀ i : ℕ, Module.Free R (F i))
    (a₀ : F 0 ⟶ N' 0) (ha₀ : δ 0 ≫ a₀ ≫ η = 0) :
    ∃ α : ∀ i : ℕ, F i ⟶ N' i,
      α 0 = a₀ ∧ (∀ i : ℕ, α (i + 1) ≫ d i = δ i ≫ α i) := by
  classical
  have (i : ℕ) : Module.Free R (F i) := hfree i
  have (i : ℕ) : Projective (F i) := inferInstance
  let a₁ := hex0.liftFromProjective (δ 0 ≫ a₀) (by simpa only [Category.assoc] using ha₀)
  have ha₁ : a₁ ≫ d 0 = δ 0 ≫ a₀ := hex0.liftFromProjective_comp _ _
  let P := fun i : ℕ ↦ Σ' a : F i ⟶ N' i,
    Σ' b : F (i + 1) ⟶ N' (i + 1), b ≫ d i = δ i ≫ a
  let step : ∀ i : ℕ, P i → P (i + 1) := fun i p ↦ by
    have hz : (δ (i + 1) ≫ p.2.1) ≫ d i = 0 := by
      rw [Category.assoc, p.2.2, ← Category.assoc, hδ i, Limits.zero_comp]
    exact ⟨p.2.1, (hex i).liftFromProjective (δ (i + 1) ≫ p.2.1) hz,
      (hex i).liftFromProjective_comp _ _⟩
  let p : ∀ i : ℕ, P i := fun i ↦ Nat.rec ⟨a₀, a₁, ha₁⟩ step i
  refine ⟨fun i ↦ (p i).1, rfl, ?_⟩
  intro i
  exact (p i).2.2
