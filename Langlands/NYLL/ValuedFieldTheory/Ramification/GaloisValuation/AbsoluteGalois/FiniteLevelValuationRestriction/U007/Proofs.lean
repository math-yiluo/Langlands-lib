/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/- Modifications by Worker 256, with proof guidance by Worker 122 (2026-11-13):
   extract M233.007 from upstream commit
   fbd320cd8b1b06487c58227e92eb135794267709,
   FiniteLevelValuationRestriction.lean lines 132-148. Prefix the namespace
   with Langlands.NYLL, qualify Mathlib valuation names and introduce the
   published closed target telescope. Preserve the source proof except
   omit the unused mem_restrictIntermediateField_iff simp argument, which
   triggers an unused-simp-argument warning with the pinned Mathlib.
   Replace upstream imports by the published Statements module.
   Original LICENSE and NOTICE are retained in licenses/NYLL/. -/

import Langlands.NYLL.ValuedFieldTheory.Ramification.GaloisValuation.AbsoluteGalois.FiniteLevelValuationRestriction.Statements

namespace Langlands.NYLL.RamificationTheory.ValuationSubring

universe u v w

/-- M233.007: restriction to an intermediate field preserves valuation extension. -/
theorem restrictIntermediateField_hasExtension :
    restrictIntermediateField_hasExtensionStatement.{u, v, w} := by
  intro K Ω _ _ _ Γ _ v A _ E
  apply _root_.Valuation.HasExtension.ofComapInteger
  ext x
  simp only [Subring.mem_comap, Valuation.mem_integer_iff,
    _root_.ValuationSubring.valuation_le_one_iff]
  change algebraMap E Ω (algebraMap K E x) ∈ A ↔ v x ≤ 1
  rw [← IsScalarTower.algebraMap_apply K E Ω x]
  rw [← A.valuation_le_one_iff (algebraMap K Ω x)]
  exact _root_.Valuation.HasExtension.val_map_le_one_iff
    (vR := v) (vA := A.valuation) x

end Langlands.NYLL.RamificationTheory.ValuationSubring
