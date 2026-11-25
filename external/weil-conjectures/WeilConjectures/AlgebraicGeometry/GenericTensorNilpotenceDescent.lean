/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Away.Basic

import Mathlib.Tactic.Ring

/-! # Nilpotence in a generic tensor fiber -/

@[expose] public section

set_option autoImplicit false

universe u v w z

open scoped TensorProduct

/-- Inverting an annihilator descends generic nilpotence.

Source: smooth purity blueprint, `sk-prop-sf-cbc`,
`lem-weil-pbc-finite-pushforward-generic-constructible`, proof steps 4--9;
localization descent in `lem-weil-pbc-generic-product-kernel-bound`.
(blueprint: lem-weil-pbc-generic-tensor-nilpotence-descent)

Proof: B tensor_A R is the localization of B tensor_A R0 at the powers of
1 tensor s. Hence each x has the form y/(1 tensor s)^n. If its generic image
is nilpotent, the generic image of y is nilpotent, since the denominator is
invertible in F. The hypothesis gives that (1 tensor t) times y is nilpotent.
Since t divides s, the image of t is a unit in R, and so is 1 tensor its image
in the tensor algebra. It follows that the image of y, and then x, is nilpotent.
If s is zero, a localization is the zero ring and the conclusion is immediate;
with the asserted fraction-field structure this case has no instances. No
nontriviality of B, nor any generic splitting, is used in this argument. -/
theorem generic_tensor_nilpotence_of_annihilator
    (A : Type u) [CommRing A]
    (B : Type v) [CommRing B] [Algebra A B]
    (R0 : Type w) [CommRing R0] [Algebra A R0]
    (F : Type z) [Field F] [Algebra A F] [Algebra R0 F]
    [IsScalarTower A R0 F]
    (t : R0)
    (ht : ∀ x : B ⊗[A] R0,
      IsNilpotent (Algebra.TensorProduct.map (AlgHom.id A B)
        (IsScalarTower.toAlgHom A R0 F) x) →
      IsNilpotent ((1 : B) ⊗ₜ[A] t * x))
    (s : R0) (hts : t ∣ s)
    (R : Type u) [CommRing R] [Algebra R0 R] [IsLocalization.Away s R]
    [Algebra A R] [IsScalarTower A R0 R] [Algebra R F]
    [IsScalarTower R0 R F] [IsScalarTower A R F] [IsFractionRing R F]
    (x : B ⊗[A] R) :
    IsNilpotent (Algebra.TensorProduct.map (AlgHom.id A B)
      (IsScalarTower.toAlgHom A R F) x) → IsNilpotent x := by
  let l := Algebra.TensorProduct.map (AlgHom.id A B) (IsScalarTower.toAlgHom A R0 R)
  let m := Algebra.TensorProduct.map (AlgHom.id A B) (IsScalarTower.toAlgHom A R F)
  let m0 := Algebra.TensorProduct.map (AlgHom.id A B) (IsScalarTower.toAlgHom A R0 F)
  let d : B ⊗[A] R := (1 : B) ⊗ₜ[A] (algebraMap R0 R s)
  have hden (z : B ⊗[A] R) : ∃ n : ℕ, ∃ y : B ⊗[A] R0, z * d ^ n = l y := by
    induction z using TensorProduct.inductionOn with
    | tmul b c =>
      obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj s c
      refine ⟨n, b ⊗ₜ[A] a, ?_⟩
      simpa [d, l, Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.tmul_mul_tmul]
        using congrArg (fun r ↦ b ⊗ₜ[A] r) ha
    | add z w hz hw =>
      obtain ⟨n, y, hy⟩ := hz
      obtain ⟨k, v, hv⟩ := hw
      refine ⟨n + k, y * ((1 : B) ⊗ₜ[A] s) ^ k +
        v * ((1 : B) ⊗ₜ[A] s) ^ n, ?_⟩
      have hd : l ((1 : B) ⊗ₜ[A] s) = d := rfl
      rw [map_add, map_mul, map_mul, map_pow, map_pow, hd, ← hy, ← hv, pow_add]
      ring
  have hcomp (y : B ⊗[A] R0) : m (l y) = m0 y := by
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => simp [hy, hz]
    | tmul b c =>
      simp only [l, m, m0, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      change b ⊗ₜ[A] (algebraMap R F (algebraMap R0 R c)) =
        b ⊗ₜ[A] (algebraMap R0 F c)
      rw [← IsScalarTower.algebraMap_apply R0 R F]
  intro hx
  obtain ⟨n, y, hy⟩ := hden x
  have hmy : IsNilpotent (m0 y) := by
    rw [← hcomp, ← hy, map_mul]
    exact (Commute.all _ _).isNilpotent_mul_right hx
  have hty := (ht y hmy).map l
  have he : l ((1 : B) ⊗ₜ[A] t * y) =
      ((1 : B) ⊗ₜ[A] (algebraMap R0 R t)) * (x * d ^ n) := by
    rw [map_mul, ← hy]
    rfl
  rw [he] at hty
  have hut : IsUnit ((1 : B) ⊗ₜ[A] (algebraMap R0 R t)) :=
    (IsLocalization.Away.isUnit_of_dvd s hts).map
      (Algebra.TensorProduct.includeRight (R := A) (A := B))
  have hud : IsUnit d :=
    (IsLocalization.Away.algebraMap_isUnit s).map
      (Algebra.TensorProduct.includeRight (R := A) (A := B))
  have hxy : IsNilpotent (x * d ^ n) :=
    (hut.isNilpotent_unit_mul_of_commute_iff (Commute.all _ _)).mp hty
  exact ((hud.pow n).isNilpotent_mul_unit_of_commute_iff (Commute.all _ _)).mp hxy
