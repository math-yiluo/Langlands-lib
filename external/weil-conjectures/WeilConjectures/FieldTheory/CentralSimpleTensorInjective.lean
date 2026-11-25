/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.BrauerGroup.Defs
public import Mathlib.Algebra.Azumaya.Defs

import WeilConjectures.Mathlib.Algebra.Central.TensorProduct
import Mathlib.RingTheory.TwoSidedIdeal.Operations

@[expose] public section

universe u

namespace Field

-- Generalize the coordinate proof in
-- WeilConjectures.Mathlib.Algebra.Central.TensorProduct to a noncommutative left factor.
-- Central coefficients become elements of includeLeft.range, rather than scalars over F.
open TensorProduct Algebra.TensorProduct in
private lemma mem_left_range_of_forall_commute_one_tmul
    {K F A : Type*} [CommRing K] [Ring F] [Algebra K F] [Module.Free K F]
    [Ring A] [Algebra K A] [Algebra.IsCentral K A]
    (x : F ⊗[K] A) (hx : ∀ a : A, (1 ⊗ₜ a) * x = x * (1 ⊗ₜ a)) :
    x ∈ (Algebra.TensorProduct.includeLeft : F →ₐ[K] F ⊗[K] A).range := by
  classical
  let b := Module.Free.chooseBasis K F
  rw [← (equivFinsuppOfBasisLeft b).symm_apply_apply x, equivFinsuppOfBasisLeft_symm_apply]
  refine Subalgebra.sum_mem _ fun j _ ↦ ?_
  have hc : equivFinsuppOfBasisLeft b x j ∈ Subalgebra.center K A := by
    rw [Subalgebra.mem_center_iff]
    intro a
    rw [← equivFinsuppOfBasisLeft_one_tmul_mul, hx, equivFinsuppOfBasisLeft_mul_one_tmul]
  obtain ⟨c, hc⟩ := Algebra.mem_bot.mp (Algebra.IsCentral.out hc)
  dsimp only
  rw [← hc, Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul]
  exact ⟨c • b j, rfl⟩

-- Normalize a nonzero coefficient of a minimum-support ideal element to one.
-- Every commutator then has strictly smaller support, so it vanishes.
open TensorProduct Algebra.TensorProduct in
private lemma exists_ne_zero_mem_left_range_of_ne_bot {K F A : Type*} [CommRing K] [Ring F]
    [Algebra K F] [Module.Free K F] [Ring A] [Algebra K A] [Algebra.IsCentral K A]
    [IsSimpleRing A] (I : TwoSidedIdeal (F ⊗[K] A)) (hI : I ≠ ⊥) :
    ∃ x ∈ I, x ≠ 0 ∧ x ∈ (Algebra.TensorProduct.includeLeft : F →ₐ[K] F ⊗[K] A).range := by
  classical
  let e := equivFinsuppOfBasisLeft (Module.Free.chooseBasis K F) (N := A)
  have hex : ∃ n, ∃ x ∈ I, x ≠ 0 ∧ (e x).support.card = n := by
    by_contra! h
    refine hI (eq_bot_iff.mpr fun x hx ↦ ?_)
    rw [TwoSidedIdeal.mem_bot]
    by_contra hx0
    exact h _ x hx hx0 rfl
  obtain ⟨x, hxI, hx0, hxn⟩ := Nat.find_spec hex
  obtain ⟨j₀, hj₀⟩ := Finsupp.ne_iff.mp ((map_ne_zero_iff e e.injective).mpr hx0)
  let J : TwoSidedIdeal A := .mk' {y | ∃ z ∈ I, (∀ j, e x j = 0 → e z j = 0) ∧ e z j₀ = y}
    ⟨0, I.zero_mem, by simp, by simp⟩
    (fun ⟨z, hz, hzs, hzj⟩ ⟨z', hz', hzs', hzj'⟩ ↦ ⟨z + z', I.add_mem hz hz',
      fun j hj ↦ by simp [hzs j hj, hzs' j hj], by simp [hzj, hzj']⟩)
    (fun ⟨z, hz, hzs, hzj⟩ ↦ ⟨-z, I.neg_mem hz, fun j hj ↦ by simp [hzs j hj], by simp [hzj]⟩)
    (fun {a} _ ⟨z, hz, hzs, hzj⟩ ↦ ⟨(1 ⊗ₜ a) * z, I.mul_mem_left _ _ hz,
      fun j hj ↦ by rw [equivFinsuppOfBasisLeft_one_tmul_mul, hzs j hj, mul_zero],
      by rw [equivFinsuppOfBasisLeft_one_tmul_mul, hzj]⟩)
    (fun {_ a} ⟨z, hz, hzs, hzj⟩ ↦ ⟨z * (1 ⊗ₜ a), I.mul_mem_right _ _ hz,
      fun j hj ↦ by rw [equivFinsuppOfBasisLeft_mul_one_tmul, hzs j hj, zero_mul],
      by rw [equivFinsuppOfBasisLeft_mul_one_tmul, hzj]⟩)
  have h1 : (1 : A) ∈ J := IsSimpleRing.one_mem_of_ne_zero_mem J hj₀
    ((TwoSidedIdeal.mem_mk' _ _ _ _ _ _ _).mpr ⟨x, hxI, fun _ h ↦ h, rfl⟩)
  obtain ⟨z, hzI, hzs, hz1⟩ := (TwoSidedIdeal.mem_mk' _ _ _ _ _ _ _).mp h1
  refine ⟨z, hzI, ?_, mem_left_range_of_forall_commute_one_tmul z fun a ↦ ?_⟩
  · rintro rfl
    simp at hz1
  by_contra hne
  have hy (j) : e ((1 ⊗ₜ a) * z - z * (1 ⊗ₜ a)) j = a * e z j - e z j * a := by
    rw [map_sub, Finsupp.sub_apply, equivFinsuppOfBasisLeft_one_tmul_mul,
      equivFinsuppOfBasisLeft_mul_one_tmul]
  have hsub : (e ((1 ⊗ₜ a) * z - z * (1 ⊗ₜ a))).support ⊆ (e x).support.erase j₀ := by
    intro j hj
    rw [Finsupp.mem_support_iff, hy] at hj
    rw [Finset.mem_erase, Finsupp.mem_support_iff]
    refine ⟨?_, fun h ↦ hj ?_⟩
    · rintro rfl
      simp [hz1] at hj
    · simp [hzs j h]
  refine Nat.find_min hex ?_ ⟨_, I.sub_mem (I.mul_mem_left _ _ hzI) (I.mul_mem_right _ _ hzI),
    sub_ne_zero.mpr hne, rfl⟩
  rw [← hxn]
  exact (Finset.card_le_card hsub).trans_lt
    (Finset.card_erase_lt_of_mem (Finsupp.mem_support_iff.mpr hj₀))

-- A nonzero ideal meets the left factor; simplicity of that factor gives one.
open TensorProduct Algebra.TensorProduct in
private lemma simple_tensor_of_central
    {K F A : Type*} [Field K] [Ring F] [Algebra K F] [IsSimpleRing F]
    [Ring A] [Algebra K A] [Algebra.IsCentral K A] [IsSimpleRing A] :
    IsSimpleRing (F ⊗[K] A) := by
  have : Nontrivial (F ⊗[K] A) := (Algebra.TensorProduct.includeLeft_injective (S := K)
    (FaithfulSMul.algebraMap_injective K A)).nontrivial
  refine IsSimpleRing.of_eq_bot_or_eq_top fun I ↦ or_iff_not_imp_left.mpr fun hI ↦ ?_
  obtain ⟨x, hxI, hx0, hx⟩ := exists_ne_zero_mem_left_range_of_ne_bot I hI
  obtain ⟨f, rfl⟩ := hx
  let i : F →ₐ[K] F ⊗[K] A := Algebra.TensorProduct.includeLeft
  have hf : f ≠ 0 := by
    rintro rfl
    exact hx0 (map_zero i)
  have h1 : (1 : F) ∈ I.comap i.toRingHom :=
    IsSimpleRing.one_mem_of_ne_zero_mem _ hf ((TwoSidedIdeal.mem_comap i.toRingHom).mpr hxI)
  exact I.eq_top (by simpa using ((TwoSidedIdeal.mem_comap i.toRingHom).mp h1))

/-- Injectivity of the enveloping map for a finite-dimensional central simple algebra.

Proof: taking the opposite preserves finite dimension, centrality and simplicity.
Stacks Tag 074G therefore makes `A ⊗[K] Aᵐᵒᵖ` simple. The kernel of the unital
algebra homomorphism `a ⊗ op(b) ↦ (v ↦ a * v * b)` is a two-sided ideal, so it is
zero or the whole domain. It cannot be the whole domain: the map sends one to the
identity endomorphism of the nonzero algebra A, and that endomorphism is not zero
(evaluate it at one). Thus its kernel is zero. If two elements have the same image,
their difference belongs to this zero kernel, so the elements are equal.
Source: Stacks Project, Tag 074I, Lemma 11.4.10, proof; tensor simplicity in
Tag 074G, Lemma 11.4.8.
(blueprint: lem-sc-central-simple-tensor-end-injective). -/
theorem centralSimple_mulLeftRight_injective (K : Type u) [Field K] (A : CSA.{u, u} K) :
    Function.Injective (AlgHom.mulLeftRight K A) := by
  have : IsSimpleRing (TensorProduct K A Aᵐᵒᵖ) := simple_tensor_of_central
  exact (AlgHom.mulLeftRight K A).toRingHom.injective

end Field
