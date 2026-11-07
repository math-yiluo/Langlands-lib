/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Adapted by Worker 1686 from ClassFieldTheory commit
fbd320cd8b1b06487c58227e92eb135794267709:
isolate M422.005 in Langlands.NYLL and prove the exact published universal
statement. Use the published smallness theorem and transported valuation
and relation locally, preserving the original witness-transfer proof.
The original license and notice are retained in licenses/NYLL/LICENSE and
licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ShrinkNontrivialStatement

/-!
# Nontriviality of the transported valuative relation

Pull a nontrivial valuation witness back along `Shrink.ringEquiv` and apply
the nontriviality criterion for the published transported relation.
-/

namespace Langlands.NYLL.LocalFieldTheory

open ValuativeRel

universe u

/-- The published valuative relation on the universe-zero representative of
every nonarchimedean local field is nontrivial. -/
theorem shrinkLocalField_isNontrivial : shrinkLocalField_isNontrivialStatement.{u} := by
  intro K _ _ _ _
  let : Small.{0} K := nonarchimedeanLocalField_small K
  let : ValuativeRel (Shrink.{0} K) := shrinkLocalFieldValuativeRel K
  let v := shrinkLocalFieldValuation K
  let : v.Compatible := Valuation.Compatible.ofValuation v
  have hvK : (valuation K).IsNontrivial :=
    (ValuativeRel.isNontrivial_iff_isNontrivial (valuation K)).mp inferInstance
  have hvS : v.IsNontrivial := by
    obtain ⟨x, hx0, hx1⟩ := hvK.exists_val_nontrivial
    refine ⟨(Shrink.ringEquiv K).symm x, ?_, ?_⟩
    · simpa [v, shrinkLocalFieldValuation] using hx0
    · simpa [v, shrinkLocalFieldValuation] using hx1
  exact (ValuativeRel.isNontrivial_iff_isNontrivial v).2 hvS

end Langlands.NYLL.LocalFieldTheory
