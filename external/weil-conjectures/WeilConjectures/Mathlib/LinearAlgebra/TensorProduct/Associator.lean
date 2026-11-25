/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Associator

/-!
# Tensor products of free rank-one modules

If `a` and `b` are free generators of the `R`-modules `A` and `B`, i.e. `r ↦ r • a` and
`r ↦ r • b` are bijective, then `a ⊗ₜ b` is a free generator of `A ⊗[R] B`
(`TensorProduct.bijective_smul_tmul`), and `x ↦ x ⊗ₜ b` is a bijection `A → A ⊗[R] B`
(`TensorProduct.bijective_tmul_right_of_bijective_smul`).
-/

@[expose] public section

/-- **The tensor product of free generators is a free generator.** If `r ↦ r • a` and
`r ↦ r • b` are bijective, so is `r ↦ r • (a ⊗ₜ b)`. -/
lemma TensorProduct.bijective_smul_tmul {R A B : Type*} [CommRing R] [AddCommGroup A]
    [Module R A] [AddCommGroup B] [Module R B] {a : A} {b : B}
    (ha : Function.Bijective fun r : R ↦ r • a) (hb : Function.Bijective fun r : R ↦ r • b) :
    Function.Bijective fun r : R ↦ r • (a ⊗ₜ[R] b) := by
  let eA := LinearEquiv.ofBijective (LinearMap.toSpanSingleton R A a) ha
  let eB := LinearEquiv.ofBijective (LinearMap.toSpanSingleton R B b) hb
  have : (fun r : R ↦ r • (a ⊗ₜ[R] b)) =
      TensorProduct.congr eA eB ∘ (TensorProduct.lid R R).symm := by
    funext r
    simp [eA, eB, TensorProduct.tmul_smul]
  rw [this]
  exact (TensorProduct.congr eA eB).bijective.comp (TensorProduct.lid R R).symm.bijective

/-- If `e` is a basis of a free module `B` of rank one, i.e. `r ↦ r • e` is bijective, then
`a ↦ a ⊗ₜ e` is a bijection `A → A ⊗[R] B`. -/
lemma TensorProduct.bijective_tmul_right_of_bijective_smul {R A B : Type*} [CommRing R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] {e : B}
    (he : Function.Bijective fun r : R ↦ r • e) :
    Function.Bijective fun a : A ↦ a ⊗ₜ[R] e := by
  have he' : Function.Bijective (LinearMap.toSpanSingleton R B e) := he
  let f : R ≃ₗ[R] B := LinearEquiv.ofBijective (LinearMap.toSpanSingleton R B e) he'
  have : (fun a : A ↦ a ⊗ₜ[R] e) =
      TensorProduct.congr (LinearEquiv.refl R A) f ∘ (TensorProduct.rid R A).symm := by
    ext a
    simp only [f, Function.comp_apply, TensorProduct.rid_symm_apply, TensorProduct.congr_tmul,
      LinearEquiv.refl_apply]
    rw [LinearEquiv.ofBijective_apply, LinearMap.toSpanSingleton_apply, one_smul]
  rw [this]
  exact (EquivLike.bijective _).comp (EquivLike.bijective _)
