/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Noetherian.Defs

import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Module.Torsion.Basic

/-! # Nilpotence in a generic tensor fiber -/

@[expose] public section

set_option autoImplicit false

universe u v w z

open scoped TensorProduct

/-- One scalar makes every generically nilpotent element nilpotent.

Source: smooth purity blueprint, `sk-prop-sf-cbc`,
`lem-weil-pbc-finite-pushforward-generic-constructible`, proof steps 4--9;
the finite torsion-kernel argument in `lem-weil-pbc-generic-product-kernel-bound`.
(blueprint: lem-weil-pbc-generic-tensor-nilpotence-annihilator)

Proof: Let C be the quotient of B tensor_A R0 by its nilradical. This is finite
as an R0-module, since base extension and quotients preserve module finiteness.
Its map to the reduction of B tensor_A F is localization at the nonzero elements
of R0: tensor products and reduction commute with localization. The kernel N is
therefore torsion. Since R0 is Noetherian, N is finitely generated. Choose finite
module generators of N and a nonzero annihilator for each generator. Their product
t is nonzero because R0 is a domain, and annihilates N by linearity. In the empty
case choose t = 1. If x has nilpotent generic image, its class lies in N, so the
class of t smul x is zero. Thus t smul x belongs to the nilradical, as asserted. -/
theorem exists_generic_tensor_nilpotence_annihilator
    (A : Type u) [CommRing A]
    (B : Type v) [CommRing B] [Algebra A B] [Module.Finite A B]
    (R0 : Type w) [CommRing R0] [IsNoetherianRing R0] [IsDomain R0]
    [Algebra A R0]
    (F : Type z) [Field F] [Algebra A F] [Algebra R0 F]
    [IsScalarTower A R0 F] [IsFractionRing R0 F] :
    ∃ t : R0, t ≠ 0 ∧ ∀ x : B ⊗[A] R0,
      IsNilpotent (Algebra.TensorProduct.map (AlgHom.id A B)
        (IsScalarTower.toAlgHom A R0 F) x) →
      IsNilpotent ((1 : B) ⊗ₜ[A] t * x) := by
  classical
  let C := B ⊗[A] R0
  let D := B ⊗[A] F
  let m : C →ₐ[A] D :=
    Algebra.TensorProduct.map (AlgHom.id A B) (IsScalarTower.toAlgHom A R0 F)
  let : Algebra R0 C := Algebra.TensorProduct.rightAlgebra
  let : Algebra C D := m.toAlgebra
  let : IsScalarTower B C D := IsScalarTower.of_algebraMap_eq fun b ↦ by
    change b ⊗ₜ[A] (1 : F) = m (b ⊗ₜ[A] (1 : R0))
    change b ⊗ₜ[A] (1 : F) = b ⊗ₜ[A] (IsScalarTower.toAlgHom A R0 F (1 : R0))
    rw [map_one]
  have hloc := IsLocalization.tensorProduct_tensorProduct_right A B
    (nonZeroDivisors R0) F (by
      ext a
      change m ((1 : B) ⊗ₜ[A] a) = (1 : B) ⊗ₜ[A] (algebraMap R0 F a)
      rfl)
  let M : Submonoid C := (nonZeroDivisors R0).map
    (Algebra.TensorProduct.includeRight (R := A) (A := B))
  have htors (x : C) (hx : IsNilpotent (m x)) :
      ∃ a : R0, a ≠ 0 ∧ IsNilpotent ((1 : B) ⊗ₜ[A] a * x) := by
    obtain ⟨n, hn⟩ := hx
    have hz : algebraMap C D (x ^ n) = 0 := by
      change m (x ^ n) = 0
      rwa [map_pow]
    obtain ⟨a, ha⟩ := (IsLocalization.map_eq_zero_iff M D (x ^ n)).mp hz
    obtain ⟨a0, ha0, he⟩ := a.property
    have hzero : ((1 : B) ⊗ₜ[A] a0) * x ^ n = 0 := by
      rw [← he] at ha
      exact ha
    refine ⟨a0, nonZeroDivisors.ne_zero ha0, ?_⟩
    by_cases hn0 : n = 0
    · subst n
      refine ⟨1, ?_⟩
      simp only [pow_zero, mul_one] at hzero
      simp [hzero]
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
      refine ⟨k + 1, ?_⟩
      rw [mul_pow, pow_succ, mul_assoc, hzero, mul_zero]
  let Q := C ⧸ nilradical C
  let q : C →+* Q := Ideal.Quotient.mk _
  let J : Ideal C := (nilradical D).comap m
  let N : Ideal Q := J.map q
  have : Module.Finite R0 C := Module.Finite.of_surjective
    (Algebra.TensorProduct.commRight A R0 B).toLinearMap
    (Algebra.TensorProduct.commRight A R0 B).surjective
  have hN : Module.IsTorsion R0 N := by
    intro z
    obtain ⟨x, hx, he⟩ :=
      (Ideal.mem_map_iff_of_surjective q Ideal.Quotient.mk_surjective).mp z.property
    obtain ⟨a, ha, hax⟩ := htors x (mem_nilradical.mp hx)
    refine ⟨⟨a, mem_nonZeroDivisors_iff_ne_zero.mpr ha⟩, ?_⟩
    apply Subtype.ext
    change a • (z : Q) = 0
    rw [← he]
    change q ((1 : B) ⊗ₜ[A] a) * q x = 0
    rw [← map_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (mem_nilradical.mpr hax)
  obtain ⟨t, htN, ht⟩ :=
    Submodule.annihilator_top_inter_nonZeroDivisors (R := R0) (M := N) hN
  refine ⟨t, nonZeroDivisors.ne_zero ht, ?_⟩
  intro x hx
  have hxJ : x ∈ J := mem_nilradical.mpr hx
  have hqx : q x ∈ N := Ideal.mem_map_of_mem q hxJ
  have hz : t • (⟨q x, hqx⟩ : N) = 0 :=
    Submodule.mem_annihilator.mp htN _ Submodule.mem_top
  have hz' : q ((1 : B) ⊗ₜ[A] t * x) = 0 := by
    have hh : t • q x = 0 := congrArg (fun z : N ↦ (z : Q)) hz
    change q ((1 : B) ⊗ₜ[A] t) * q x = 0 at hh
    rwa [map_mul]
  exact mem_nilradical.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz')
