/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 212 on 2026-11-13: extracted M133.020 from
IdealQuotients.lean at fbd320cd8b1b06487c58227e92eb135794267709; added Langlands.NYLL
and the exact named statement target. Local prerequisite adaptations and
private helpers are documented in the paired Markdown.
LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients.Statements

namespace Langlands.NYLL.LocalFieldTheory

universe u

open scoped ValuativeRel

private theorem chosenIrreducible
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    Irreducible (chosenIntegerRingUniformizer K) :=
  Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible 𝒪[K])

/-- Proof of the exact source-adapted M133.020 target. -/
theorem exists_chosenIntegerRingUniformizer_pow_mul_mem_integerRing
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x : K) :
    exists_chosenIntegerRingUniformizer_pow_mul_mem_integerRingStatement K x := by
  change ∃ n : Nat, (((chosenIntegerRingUniformizer K : 𝒪[K]) : K) ^ n) * x ∈ 𝒪[K]
  obtain ⟨a, b, hb, hfrac⟩ := IsFractionRing.div_surjective (A := 𝒪[K]) x
  have hb_ne : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨n, u, hb_factor⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb_ne
      (chosenIrreducible K)
  refine ⟨n, ?_⟩
  rw [← hfrac, hb_factor]
  have hϖ_ne : (((chosenIntegerRingUniformizer K : 𝒪[K]) : K)) ≠ 0 := by
    intro h
    exact (chosenIrreducible K).ne_zero
      ((IsFractionRing.injective 𝒪[K] K) h)
  have hϖ_pow_ne :
      (((chosenIntegerRingUniformizer K : 𝒪[K]) : K) ^ n) ≠ 0 :=
    pow_ne_zero n hϖ_ne
  have hu_ne : (((u : 𝒪[K]) : K)) ≠ 0 := by
    intro h
    exact u.ne_zero ((IsFractionRing.injective 𝒪[K] K) h)
  have hclear :
      (((chosenIntegerRingUniformizer K : 𝒪[K]) : K) ^ n) *
          ((a : K) /
            (((u : 𝒪[K]) * chosenIntegerRingUniformizer K ^ n : 𝒪[K]) : K)) =
        ((a * ↑u⁻¹ : 𝒪[K]) : K) := by
    calc
      (((chosenIntegerRingUniformizer K : 𝒪[K]) : K) ^ n) *
          ((a : K) /
            (((u : 𝒪[K]) * chosenIntegerRingUniformizer K ^ n : 𝒪[K]) : K))
          =
          (((chosenIntegerRingUniformizer K : 𝒪[K]) : K) ^ n) *
            ((a : K) / (((u : 𝒪[K]) : K) *
              (((chosenIntegerRingUniformizer K : 𝒪[K]) : K) ^ n))) := by
            congr 2
      _ = (a : K) * (((u : 𝒪[K]) : K))⁻¹ := by
            field_simp [hu_ne, hϖ_pow_ne]
      _ = ((a * ↑u⁻¹ : 𝒪[K]) : K) := by
            have hu_inv :
                (((↑u⁻¹ : 𝒪[K]) : K)) = (((u : 𝒪[K]) : K))⁻¹ := by
              exact map_units_inv (algebraMap 𝒪[K] K) u
            rw [← hu_inv]
            rfl
  change (((chosenIntegerRingUniformizer K : 𝒪[K]) : K) ^ n) *
      ((a : K) /
        (((u : 𝒪[K]) * chosenIntegerRingUniformizer K ^ n : 𝒪[K]) : K)) ∈ 𝒪[K]
  rw [hclear]
  exact (a * ↑u⁻¹ : 𝒪[K]).2

end Langlands.NYLL.LocalFieldTheory
