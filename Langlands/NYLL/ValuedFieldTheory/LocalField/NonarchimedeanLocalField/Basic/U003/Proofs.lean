/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 120, 13 November 2026:
Extract the proof of M128.003 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Basic.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix, import only the Basic ValuationStatements module, and
prove the published closed proposition by introducing its five binders
and the source's integer `n` in one `intro` before the original proof.
Omit the source noncomputable section and all other source declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.ValuationStatements

/-!
# Surjectivity of the normalized valuation

Every integer is the normalized valuation of a unit of a nonarchimedean
local field.
-/

namespace Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField

universe u

open scoped ValuativeRel WithZero

/-- Every integer occurs as the normalized valuation of a nonzero field element. -/
theorem v_surjective : v_surjectiveStatement.{u} := by
  intro K _ _ _ _ n
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

end Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField
