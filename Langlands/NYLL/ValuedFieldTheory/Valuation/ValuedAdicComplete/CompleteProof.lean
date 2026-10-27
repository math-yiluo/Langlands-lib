/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/- Modifications by Worker 738 (2026-10-27): extract M247.003 alone, prove the
   published closed target in Langlands.NYLL by importing the published M247.002
   adicity theorem, and use a focused import. -/

import Langlands.NYLL.ValuedFieldTheory.Valuation.ValuedAdicComplete.AdicProof

/-!
# Native maximal-ideal adic completeness

If the supplied `Valued` uniformity on a rank-one discrete valued field is
complete, then its actual valuation subring is adically complete for its actual
maximal ideal.
-/

universe u v

namespace Langlands.NYLL.ValuationTheory.Valuations

/-- Completeness of a rank-one discrete valued field for its supplied
uniformity gives maximal-ideal adic completeness of its valuation subring. -/
theorem rankOneDiscreteValuationSubring_isAdicComplete :
    RankOneDiscreteValuationSubringIsAdicCompleteStatement.{u, v} := by
  intro K _ Gamma _ _ _ _
  let val := (Valued.v : _root_.Valuation K Gamma)
  have hadic : IsAdic (IsLocalRing.maximalIdeal val.valuationSubring) :=
    rankOneDiscreteValuationSubring_isAdic.{u, v}
  let : IsUniformAddGroup val.valuationSubring :=
    val.valuationSubring.toAddSubgroup.isUniformAddGroup
  let : CompleteSpace val.valuationSubring :=
    @IsClosed.completeSpace_coe K _ _ (val.valuationSubring : Set K)
      (Valued.isClosed_valuationSubring K)
  exact hadic.isAdicComplete_iff.2 ⟨inferInstance, inferInstance⟩

end Langlands.NYLL.ValuationTheory.Valuations
