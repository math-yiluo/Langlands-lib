/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.RingTheory.Finiteness.Projective

/-!
# Finite projective modules are summands of free modules of finite rank

A finite projective module `Q` admits `ξⱼ : Q ⟶ R` and `mⱼ : R ⟶ Q` with `∑ⱼ ξⱼ ≫ mⱼ = 𝟙`.
-/

@[expose] public section

universe u

open CategoryTheory

/-- A finite projective module `Q` is a direct summand of a free module of finite rank: there are
`ξⱼ : Q ⟶ R` and `mⱼ : R ⟶ Q` with `∑ⱼ ξⱼ ≫ mⱼ = 𝟙`. -/
lemma ModuleCat.exists_sum_comp_eq_id_of_projective {R : Type u} [CommRing R]
    (Q : ModuleCat.{u} R) [Module.Finite R Q] [Module.Projective R Q] :
    ∃ (n : ℕ) (ξ : Fin n → (Q ⟶ ModuleCat.of R R)) (m : Fin n → (ModuleCat.of R R ⟶ Q)),
      ∑ j, ξ j ≫ m j = 𝟙 Q := by
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R Q
  refine ⟨n, fun j ↦ ModuleCat.ofHom (LinearMap.proj j ∘ₗ g),
    fun j ↦ ModuleCat.ofHom (f ∘ₗ LinearMap.single R (fun _ ↦ R) j), ?_⟩
  ext x
  have hx : ∑ j, LinearMap.single R (fun _ ↦ R) j (g x j) = g x := by
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  rw [ModuleCat.hom_sum, LinearMap.sum_apply]
  exact (map_sum f _ _).symm.trans ((congrArg f hx).trans congr($hfg x))

