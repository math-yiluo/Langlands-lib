/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 641 on 2026-11-14: extracted this proof into the
Langlands.NYLL namespace and made its exact published Statement the theorem
type. The paired Markdown records the proof and adaptations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U042.Statements

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients.U005.Proofs

namespace Langlands.NYLL.CyclicCohomology

noncomputable section

universe u

open scoped ValuativeRel
open Filter LocalFieldTheory

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
variable [ValuativeRel K]
variable [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable [ValuativeRel L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]

omit [FiniteDimensional K L] [IsGalois K L] in
theorem chosenBaseUniformizerPow_integerRingFieldSubmodule_mem_nhds_zero
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] (m : Nat) :
    chosenBaseUniformizerPow_integerRingFieldSubmodule_mem_nhds_zeroStatement K L m := by
  let a : L := algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ m)
  have hπ_ne : (chosenIntegerRingUniformizer K ^ m : 𝒪[K]) ≠ 0 :=
    pow_ne_zero m (chosenIntegerRingUniformizer_irreducible K).ne_zero
  have ha_ne : a ≠ 0 := by
    dsimp [a]
    change algebraMap K L ((chosenIntegerRingUniformizer K ^ m : 𝒪[K]) : K) ≠ 0
    apply (map_ne_zero (algebraMap K L)).2
    intro h
    exact hπ_ne ((IsFractionRing.injective 𝒪[K] K) h)
  have ha_val_pos : 0 < ValuativeRel.valuation L a := by
    exact (ValuativeRel.valuation L).pos_iff.2 ha_ne
  let γ : (ValuativeRel.ValueGroupWithZero L)ˣ :=
    Units.mk0 (ValuativeRel.valuation L a) (ne_of_gt ha_val_pos)
  refine Filter.mem_of_superset
    ((IsValuativeTopology.hasBasis_nhds_zero L).mem_of_mem (i := γ) trivial) ?_
  intro x hx
  change ∃ y : L, y ∈ integerRingFieldSubmodule K L ∧
    algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ m) * y = x
  refine ⟨a⁻¹ * x, ?_, ?_⟩
  · change a⁻¹ * x ∈ 𝒪[L]
    rw [Valuation.mem_integer_iff]
    have hxle : ValuativeRel.valuation L x ≤ ValuativeRel.valuation L a := le_of_lt hx
    have hval :
        ValuativeRel.valuation L (a⁻¹ * x) =
          (ValuativeRel.valuation L a)⁻¹ * ValuativeRel.valuation L x := by
      simp [map_mul]
    rw [hval]
    exact (inv_mul_le_one₀ ha_val_pos).2 hxle
  · change a * (a⁻¹ * x) = x
    rw [← mul_assoc, mul_inv_cancel₀ ha_ne, one_mul]

end
end Langlands.NYLL.CyclicCohomology
