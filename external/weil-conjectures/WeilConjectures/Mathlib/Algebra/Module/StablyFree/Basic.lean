/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.Basis.Prod

/-!
# Stably free modules and short exact sequences

Given a short exact sequence `0 → K → F → N → 0` of `R`-modules with `N` projective, the sequence
splits, so `F ≃ K × N`.

## Main results

- `Module.Projective.of_exact_of_projective`: in such a sequence with `F` projective, `K` is
  projective.
- `Module.IsStablyFree.of_exact`: in such a sequence with `F` finite free and `K` stably free, `N`
  is stably free.
-/

@[expose] public section

universe u

namespace Module

variable {R : Type u} [Ring R] {K F N : Type*} [AddCommGroup K] [Module R K] [AddCommGroup F]
  [Module R F] [AddCommGroup N] [Module R N] {f : K →ₗ[R] F} {g : F →ₗ[R] N}

/-- A short exact sequence `0 → K → F → N → 0` with `N` projective splits: `F ≃ K × N`. -/
theorem nonempty_linearEquiv_prod_of_exact [Projective R N] (hf : Function.Injective f)
    (hg : Function.Surjective g) (h : Function.Exact f g) : Nonempty (F ≃ₗ[R] K × N) := by
  obtain ⟨l, hl⟩ := projective_lifting_property g LinearMap.id hg
  exact ⟨(h.splitSurjectiveEquiv hf ⟨l, hl⟩).1⟩

/-- In a short exact sequence `0 → K → F → N → 0` with `F` and `N` projective, `K` is
projective. -/
theorem Projective.of_exact_of_projective [Projective R F] [Projective R N]
    (hf : Function.Injective f) (hg : Function.Surjective g) (h : Function.Exact f g) :
    Projective R K := by
  obtain ⟨e⟩ := nonempty_linearEquiv_prod_of_exact hf hg h
  exact .of_split (e.symm.toLinearMap ∘ₗ LinearMap.inl R K N) (LinearMap.fst R K N ∘ₗ e.toLinearMap)
    (LinearMap.ext fun x ↦ by simp)

/-- In a short exact sequence `0 → K → F → N → 0` with `F` finite and `N` projective, `K` is
finite. -/
theorem Finite.of_exact_of_projective [Module.Finite R F] [Projective R N]
    (hf : Function.Injective f) (hg : Function.Surjective g) (h : Function.Exact f g) :
    Module.Finite R K := by
  obtain ⟨e⟩ := nonempty_linearEquiv_prod_of_exact hf hg h
  exact .of_surjective (LinearMap.fst R K N ∘ₗ e.toLinearMap)
    (Prod.fst_surjective.comp e.surjective)

/-- In a short exact sequence `0 → K → F → N → 0` with `F` finite free, `K` stably free and `N`
projective, `N` is stably free. -/
theorem IsStablyFree.of_exact [Module.Finite R F] [Free R F] [IsStablyFree R K] [Projective R N]
    (hf : Function.Injective f) (hg : Function.Surjective g) (h : Function.Exact f g) :
    IsStablyFree R N := by
  obtain ⟨e⟩ := nonempty_linearEquiv_prod_of_exact hf hg h
  have : Module.Finite R K := Finite.of_exact_of_projective hf hg h
  obtain ⟨Q, _, _, _, _, _⟩ := IsStablyFree.exist_free_prod R K
  have : Free R (N × (K × Q)) := .of_equiv <| e.prodCongr (LinearEquiv.refl R Q) ≪≫ₗ
    (LinearEquiv.prodComm R K N).prodCongr (LinearEquiv.refl R Q) ≪≫ₗ
    LinearEquiv.prodAssoc R N K Q
  exact .of_free_prod R N (K × Q)

end Module
