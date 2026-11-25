/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Injectivity of maps out of an extension of scalars along a field

Let `f : R →+* S` be a ring morphism from a field `R`, and `g : X ⟶ Y` an `R`-linear map from
an `R`-module `X` to an `S`-module `Y`. Suppose that `X` and `Y` embed into spaces of functions
on a set `T`, with values in `R` and `S` respectively, compatibly with `g`. Then the
`S`-linear map `S ⊗_R X ⟶ Y`, `s ⊗ x ↦ s • g x`, adjoint to `g`, is injective
(`ModuleCat.injective_homEquiv_symm_of_eval`): writing an element of `S ⊗_R X` as
`∑ᵢ bᵢ ⊗ xᵢ` for an `R`-basis `(bᵢ)` of `S`, its image evaluated at `t` is `∑ᵢ f (xᵢ t) bᵢ`, whose
vanishing forces every `xᵢ t` to vanish.

This is the injectivity of `S ⊗_R C(T, R) ⟶ C(T, S)`, for instance for an extension of
nonarchimedean fields.
-/

@[expose] public section

open CategoryTheory TensorProduct

namespace ModuleCat

universe v u₁ u₂

variable {R : Type u₁} {S : Type u₂} [Field R] [CommRing S] (f : R →+* S)

set_option backward.isDefEq.respectTransparency false in
/-- The map `S ⊗_R X ⟶ Y` adjoint to `g : X ⟶ Y` is injective when `R` is a field and `X`, `Y`
embed compatibly into functions on a set `T` with values in `R`, `S`. -/
lemma injective_homEquiv_symm_of_eval {X : ModuleCat.{max v u₂} R} {Y : ModuleCat.{max v u₂} S}
    (g : X ⟶ (restrictScalars f).obj Y) {T : Type*} (evX : T → X →ₗ[R] R)
    (evY : T → Y →ₗ[S] S) (hX : ∀ x, (∀ t, evX t x = 0) → x = 0)
    (hg : ∀ t x, evY t (g x) = f (evX t x)) :
    Function.Injective (((extendRestrictScalarsAdj f).homEquiv X Y).symm g).hom := by
  let : Module R S := Module.compHom S f
  let b := Module.Basis.ofVectorSpace R ((restrictScalars f).obj (of S S))
  classical
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz
  obtain ⟨c, rfl⟩ := (equivFinsuppOfBasisLeft b).symm.surjective z
  suffices c = 0 by simp [this]
  have key : ∀ t, (c.sum fun i x ↦ evX t x • (b i : S)) = 0 := by
    intro t
    have h1 := congrArg (evY t) hz
    rw [map_zero, equivFinsuppOfBasisLeft_symm_apply, map_finsuppSum, map_finsuppSum] at h1
    rw [← h1]
    refine Finsupp.sum_congr fun i _ ↦ ?_
    change f (evX t (c i)) * (show S from b i) = evY t ((show S from b i) • g (c i))
    rw [LinearMap.map_smul, hg, smul_eq_mul, mul_comm]
  ext i
  apply hX
  intro t
  have := linearIndependent_iff.1 b.linearIndependent (c.mapRange (evX t) (map_zero _)) (by
    rw [Finsupp.linearCombination_apply, Finsupp.sum_mapRange_index (fun i ↦ zero_smul R (b i))]
    exact key t)
  simpa using congrArg (· i) this

end ModuleCat
