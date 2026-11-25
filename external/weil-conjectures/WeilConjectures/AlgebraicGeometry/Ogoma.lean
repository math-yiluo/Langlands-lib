/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Noetherian.Basic
import WeilConjectures.RingTheory.ExistsAnnihilatorOfSubsingletonLocalizedModule

/-! # Ogoma's lemma
Source: literature/stacks-project/smoothing.tex, Smoothing Ring Maps, Lemma Tag 07FC
(blueprint: lem-weil-pbc-ogoma)
-/

@[expose] public section

universe u v

open scoped Pointwise

/-- Ogoma's lemma, following Stacks Project, Smoothing Ring Maps, Lemma Tag 07FC
(blueprint: lem-weil-pbc-ogoma). The proof follows the five steps in the node:
form the quotient of the two kernel submodules, show its localization vanishes,
use finite generation over a Noetherian ring to obtain a uniform annihilator, and
then verify the kernel equality for every positive power. -/
theorem ogoma_lemma
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (S : Submonoid A) (π : A)
    (h : {x : LocalizedModule S M | π • x = 0} =
      {x : LocalizedModule S M | π • (π • x) = 0}) :
    ∃ s : S, ∀ n : ℕ, 0 < n →
      {m : M | ((s : A)^n * π) • m = 0} =
        {m : M | (((s : A)^n * π)^2) • m = 0} := by
  let f := LocalizedModule.mkLinearMap S M
  let g : M →ₗ[A] M := π • LinearMap.id
  let K : Submodule A M := LinearMap.ker ((f.comp g).comp g)
  let N : Submodule A M := K.map g
  have hN : Subsingleton (LocalizedModule S N) := by
    rw [LocalizedModule.subsingleton_iff]
    intro x
    obtain ⟨m, hm, hmx⟩ := x.property
    have hm' : π • (π • f m) = 0 := by
      simpa [K, g, LinearMap.mem_ker] using hm
    have hπ : π • f m = 0 := by
      exact (Set.ext_iff.mp h (f m)).mpr hm'
    have hgm : f (g m) = 0 := by simpa [g] using hπ
    obtain ⟨t, ht, htm⟩ := LocalizedModule.mem_ker_mkLinearMap_iff.mp hgm
    refine ⟨t, ht, ?_⟩
    apply Subtype.ext
    change t • (x : M) = 0
    rw [← hmx]
    exact htm
  obtain ⟨s, hs, hann⟩ :=
    Module.exists_annihilator_of_subsingleton_localizedModule S N hN
  refine ⟨⟨s, hs⟩, ?_⟩
  intro n hn
  ext m
  change ((s ^ n * π) • m = 0) ↔ ((s ^ n * π) ^ 2) • m = 0
  constructor
  · intro hm
    simp only [pow_two, mul_smul, hm, smul_zero]
  · intro hm
    have hloc : f (π • (π • m)) = 0 := by
      apply LocalizedModule.eq_zero_of_smul_eq_zero (s ^ (n + n)) (S.pow_mem hs _)
      have heq : s ^ (n + n) • (π • (π • m)) = 0 := by
        have hscalar : (s ^ n * π) ^ 2 = s ^ (n + n) * (π * π) := by
          rw [pow_add, pow_two]
          ring
        rw [hscalar, mul_smul, mul_smul] at hm
        exact hm
      simp only [← f.map_smul, heq, f.map_zero]
    have hmem : m ∈ K := by
      simpa [K, g, LinearMap.mem_ker] using hloc
    have hkill : s • (π • m) = 0 := by
      have := hann ⟨g m, Submodule.mem_map.mpr ⟨m, hmem, rfl⟩⟩
      exact congrArg Subtype.val this
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    simp only [pow_succ, mul_smul, hkill, smul_zero]

