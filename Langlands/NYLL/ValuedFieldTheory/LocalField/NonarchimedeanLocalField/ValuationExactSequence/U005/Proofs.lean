/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 120, 13 November 2026:
Extract the proof of M134.005 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ValuationExactSequence.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix, import only the ValuationExactSequence
EvaluationStatements module, and prove the published closed proposition by
introducing its five binders. Since no proof of v_surjective (M128.003) is
in the Library, its original proof, from lines 57-70 of
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Basic.lean, is
inlined as a local fact, which is then used exactly as the source term
`v_surjective K`. Omit the source noncomputable section and all other source
declarations. The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence.EvaluationStatements

/-!
# Surjectivity of the bundled valuation map

Every integer is the value of the bundled normalized valuation map on the
units of a nonarchimedean local field.
-/

namespace Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField

universe u

open scoped ValuativeRel WithZero

/-- Every integer is the valuation of some field unit. -/
theorem valuationMap_surjective : valuationMap_surjectiveStatement.{u} := by
  intro K _ _ _ _
  -- The source proof of `v_surjective K` (M128.003), inlined.
  have hv : Function.Surjective (v K) := by
    intro n
    let γ : ValuativeRel.ValueGroupWithZero K :=
      (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).symm
        ((Multiplicative.ofAdd n : Multiplicative Int) : WithZero (Multiplicative Int))
    obtain ⟨a, ha⟩ := ValuativeRel.valuation_surjective γ
    have hγ_ne : γ ≠ 0 := by
      exact (map_ne_zero
        (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).symm).2 WithZero.coe_ne_zero
    have ha0 : a ≠ 0 := by
      intro h
      apply hγ_ne
      simpa [h] using ha.symm
    refine ⟨Additive.ofMul (Units.mk0 a ha0), ?_⟩
    simp [v, γ, ha]
  exact hv

end Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField
