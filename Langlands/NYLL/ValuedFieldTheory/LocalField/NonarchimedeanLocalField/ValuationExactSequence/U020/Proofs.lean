/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 135, 14 November 2026:
Extract the proof of M134.020 (lines 178–207) from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ValuationExactSequence.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
Langlands.NYLL and prove the published closed statement by introducing its
telescope before the unchanged source tactic proof, which uses the
published M134.004 theorem valuationMap_apply. Import only the target
statement module and that published proof. Omit all other source
declarations. See paired Markdown. The upstream LICENSE and NOTICE are
preserved in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence.KernelStatements
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence.U004.Proofs

/-!
# Field units of additive valuation zero

The exact proof of NYLL M134.020.
-/

namespace Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField

open scoped ValuativeRel WithZero

/-- A field unit with additive valuation zero has multiplicative valuation one. -/
theorem valuation_eq_one_of_valuationMap_eq_zero.{u} :
    valuation_eq_one_of_valuationMap_eq_zeroStatement.{u} := by
  intro K _ _ _ _ x hx
  rw [valuationMap_apply] at hx
  dsimp [v] at hx
  have hunzero :
      WithZero.unzero
        (x := (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)
          (ValuativeRel.valuation K (x : K)))
        ((map_ne_zero (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)).2
          ((Valuation.ne_zero_iff (ValuativeRel.valuation K)).2 x.ne_zero)) =
        (1 : Multiplicative Int) := by
    have h := congrArg Multiplicative.ofAdd hx
    simpa using h
  apply (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).injective
  have hcoe :
      ((WithZero.unzero
        (x := (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)
          (ValuativeRel.valuation K (x : K)))
        ((map_ne_zero (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)).2
          ((Valuation.ne_zero_iff (ValuativeRel.valuation K)).2 x.ne_zero)) :
        Multiplicative Int) : WithZero (Multiplicative Int)) =
        (1 : WithZero (Multiplicative Int)) := by
    simpa using congrArg
      (fun y : Multiplicative Int => (y : WithZero (Multiplicative Int))) hunzero
  rw [WithZero.coe_unzero] at hcoe
  simpa using hcoe

end Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField
