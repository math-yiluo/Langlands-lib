/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Algebra.Hom

/-!
# Factoring algebra maps through the base ring

An `R`-algebra map `f : S →ₐ[R] K` all of whose values lie in the image of an injective
`algebraMap R K` factors through `R`
(`AlgHom.exists_algebraMap_comp_eq_of_forall_mem_range`).
-/

@[expose] public section

/-- An `R`-algebra map into `K` whose image lies in the image of an injective `algebraMap R K`
factors through `R`. -/
lemma AlgHom.exists_algebraMap_comp_eq_of_forall_mem_range {R S K : Type*} [CommRing R]
    [CommRing S] [CommRing K] [Algebra R S] [Algebra R K]
    (hinj : Function.Injective (algebraMap R K))
    (f : S →ₐ[R] K) (h : ∀ s, f s ∈ Set.range (algebraMap R K)) :
    ∃ θ : S →ₐ[R] R, ∀ s, algebraMap R K (θ s) = f s := by
  choose g hg using h
  exact ⟨{ toFun := g
           map_one' := hinj (by simp [hg])
           map_mul' := fun x y ↦ hinj (by simp [hg])
           map_zero' := hinj (by simp [hg])
           map_add' := fun x y ↦ hinj (by simp [hg])
           commutes' := fun x ↦ hinj (by simp [hg]) }, hg⟩
