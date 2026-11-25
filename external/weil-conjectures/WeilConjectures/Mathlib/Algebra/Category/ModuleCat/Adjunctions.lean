/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# Free modules on a kernel pair

For maps of types `f g : K ⟶ S` and `c : S ⟶ T` such that `(f, g)` maps onto the kernel pair
of `c`, the sequence `R[K] → R[S] → R[T]` with first map `R[f] - R[g]` and second map `R[c]` is
exact. We also give the objectwise version for functors to types.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace ModuleCat

variable {R : Type u} [Ring R]

/-- If `(f, g) : K → S ×_T S` is surjective onto the kernel pair of `c`, then the free module
sequence `R[K] → R[S] → R[T]` with maps `R[f] - R[g]` and `R[c]` is exact. -/
lemma exact_free_of_surjective_kernelPair {K S T : Type u} (f g : K ⟶ S) (c : S ⟶ T)
    (hfg : f ≫ c = g ≫ c) (hK : ∀ x y : S, c x = c y → ∃ k, f k = x ∧ g k = y) :
    (ShortComplex.mk ((free R).map f - (free R).map g) ((free R).map c)
      (by rw [Preadditive.sub_comp, ← Functor.map_comp, ← Functor.map_comp, hfg,
        sub_self])).Exact := by
  classical
  rw [ShortComplex.moduleCat_exact_iff]
  intro (x : S →₀ R) hx
  replace hx : Finsupp.mapDomain c x = 0 := hx
  rcases isEmpty_or_nonempty S with hS | ⟨⟨s₀⟩⟩
  · exact ⟨0, Subsingleton.elim (α := S →₀ R) _ _⟩
  let σ : T → S := fun t ↦ if h : ∃ s, c s = t then h.choose else s₀
  have hσ : ∀ s, c (σ (c s)) = c s := fun s ↦ by
    have h : ∃ s', c s' = c s := ⟨s, rfl⟩
    simp only [σ, dite_eq_left h]
    exact h.choose_spec
  choose k hk₁ hk₂ using fun s ↦ hK s (σ (c s)) (hσ s).symm
  refine ⟨Finsupp.mapDomain k x, ?_⟩
  change Finsupp.mapDomain f (Finsupp.mapDomain k x) -
    Finsupp.mapDomain g (Finsupp.mapDomain k x) = x
  rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  have h₁ : (f ∘ k) = id := funext hk₁
  have h₂ : (g ∘ k) = σ ∘ c := funext hk₂
  rw [h₁, h₂, Finsupp.mapDomain_id, Finsupp.mapDomain_comp, hx, Finsupp.mapDomain_zero,
    sub_zero]

/-- Objectwise version of `ModuleCat.exact_free_of_surjective_kernelPair` for functors to
types, composed with the free module functor. -/
lemma exact_whiskeringRight_free_of_surjective_kernelPair {C : Type*} [Category C]
    {K S T : C ⥤ Type u} (f g : K ⟶ S) (c : S ⟶ T) (hfg : f ≫ c = g ≫ c)
    (hK : ∀ (j : C) (x y : S.obj j), c.app j x = c.app j y →
      ∃ k, f.app j k = x ∧ g.app j k = y) :
    (ShortComplex.mk (((Functor.whiskeringRight C _ _).obj (free R)).map f -
        ((Functor.whiskeringRight C _ _).obj (free R)).map g)
      (((Functor.whiskeringRight C _ _).obj (free R)).map c)
      (by rw [Preadditive.sub_comp, ← Functor.map_comp, ← Functor.map_comp, hfg,
        sub_self])).Exact := by
  rw [ShortComplex.exact_iff_evaluation]
  intro j
  exact exact_free_of_surjective_kernelPair (f.app j) (g.app j) (c.app j)
    (by rw [← NatTrans.comp_app, hfg, NatTrans.comp_app]) (hK j)

end ModuleCat
