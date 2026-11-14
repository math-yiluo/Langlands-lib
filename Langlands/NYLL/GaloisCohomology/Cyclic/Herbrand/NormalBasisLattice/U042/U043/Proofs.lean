/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 640 on 2026-11-14: extracted M144.043 from
NormalBasisLattice.lean at fbd320cd8b1b06487c58227e92eb135794267709,
prefixed the namespace with Langlands.NYLL, reduced imports, and stated the
result using the published proposition target. The M144.042 input is derived
locally from published irreducibility and Mathlib; see the paired Markdown.
LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U042.Statements
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients.U005.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients.U022.Proofs

namespace Langlands.NYLL.CyclicCohomology

universe u

open scoped ValuativeRel
open LocalFieldTheory

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]

/-- Powers of the chosen base uniformizer clear extension-field denominators. -/
theorem exists_chosenBaseUniformizerPow_mul_mem_integerRing_of_valuationExtension
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] (x : L) :
    exists_chosenBaseUniformizerPow_mul_mem_integerRing_of_valuationExtensionStatement K L x := by
  unfold exists_chosenBaseUniformizerPow_mul_mem_integerRing_of_valuationExtensionStatement
  obtain ⟨a, b, hb, hfrac⟩ := IsFractionRing.div_surjective (A := 𝒪[L]) x
  have hb_ne : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨m, ub, hb_factor⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb_ne
      (chosenIntegerRingUniformizer_irreducible L)
  refine ⟨m, ?_⟩
  let πK_L : 𝒪[L] :=
    integerRingMapOfValuationExtension K L (chosenIntegerRingUniformizer K)
  have hπK_L_mem : πK_L ∈ (𝓂[L] : Ideal 𝒪[L]) := by
    dsimp [πK_L]
    have hπK : chosenIntegerRingUniformizer K ∈ (𝓂[K] : Ideal 𝒪[K]) := by
      rw [(chosenIntegerRingUniformizer_irreducible K).maximalIdeal_eq]
      exact Ideal.subset_span (Set.mem_singleton (chosenIntegerRingUniformizer K))
    exact (Valuation.HasExtension.algebraMap_mem_maximalIdeal_iff
      (ValuativeRel.valuation K) (ValuativeRel.valuation L)).2 hπK
  have hπK_L_pow_mem : πK_L ^ m ∈ (𝓂[L] ^ m : Ideal 𝒪[L]) :=
    Ideal.pow_mem_pow hπK_L_mem m
  have hπK_L_span :
      πK_L ^ m ∈
        Ideal.span ({chosenIntegerRingUniformizer L ^ m} : Set 𝒪[L]) := by
    rw [← maximalIdeal_pow_eq_span_uniformizer_pow L m]
    exact hπK_L_pow_mem
  rcases Ideal.mem_span_singleton'.mp hπK_L_span with ⟨c, hc⟩
  rw [← hfrac, hb_factor]
  have hϖL_ne : (((chosenIntegerRingUniformizer L : 𝒪[L]) : L)) ≠ 0 := by
    intro h
    exact (chosenIntegerRingUniformizer_irreducible L).ne_zero
      ((IsFractionRing.injective 𝒪[L] L) h)
  have hϖL_pow_ne :
      (((chosenIntegerRingUniformizer L : 𝒪[L]) : L) ^ m) ≠ 0 :=
    pow_ne_zero m hϖL_ne
  have hub_ne : (((ub : 𝒪[L]) : L)) ≠ 0 := by
    intro h
    exact ub.ne_zero ((IsFractionRing.injective 𝒪[L] L) h)
  have hub_inv :
      (((↑ub⁻¹ : 𝒪[L]) : L)) = (((ub : 𝒪[L]) : L))⁻¹ := by
    exact map_units_inv (algebraMap 𝒪[L] L) ub
  have hbase :
      algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ m) =
        ((πK_L ^ m : 𝒪[L]) : L) := by
    dsimp [πK_L, integerRingMapOfValuationExtension]
    simp only [map_pow]
    change (algebraMap K L ((chosenIntegerRingUniformizer K : 𝒪[K]) : K)) ^ m =
      (algebraMap K L ((chosenIntegerRingUniformizer K : 𝒪[K]) : K)) ^ m
    rfl
  change algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ m) *
      ((a : L) /
        (((ub : 𝒪[L]) * chosenIntegerRingUniformizer L ^ m : 𝒪[L]) : L)) ∈ 𝒪[L]
  rw [hbase]
  have hclear :
      ((πK_L ^ m : 𝒪[L]) : L) *
          ((a : L) /
            (((ub : 𝒪[L]) * chosenIntegerRingUniformizer L ^ m : 𝒪[L]) : L)) =
        ((c * ↑ub⁻¹ * a : 𝒪[L]) : L) := by
    calc
      ((πK_L ^ m : 𝒪[L]) : L) *
          ((a : L) /
            (((ub : 𝒪[L]) * chosenIntegerRingUniformizer L ^ m : 𝒪[L]) : L))
          =
          ((c * chosenIntegerRingUniformizer L ^ m : 𝒪[L]) : L) *
            ((a : L) /
              (((ub : 𝒪[L]) * chosenIntegerRingUniformizer L ^ m : 𝒪[L]) : L)) := by
            rw [← hc]
      _ = ((c : L) * (((ub : 𝒪[L]) : L))⁻¹ * (a : L)) := by
            change
              ((c : L) * (((chosenIntegerRingUniformizer L : 𝒪[L]) : L) ^ m)) *
                  ((a : L) /
                    (((ub : 𝒪[L]) : L) *
                      (((chosenIntegerRingUniformizer L : 𝒪[L]) : L) ^ m))) =
                (c : L) * (((ub : 𝒪[L]) : L))⁻¹ * (a : L)
            field_simp [hub_ne, hϖL_pow_ne]
      _ = ((c * ↑ub⁻¹ * a : 𝒪[L]) : L) := by
            rw [← hub_inv]
            simp [mul_assoc]
  rw [hclear]
  exact (c * ↑ub⁻¹ * a : 𝒪[L]).2

end Langlands.NYLL.CyclicCohomology
