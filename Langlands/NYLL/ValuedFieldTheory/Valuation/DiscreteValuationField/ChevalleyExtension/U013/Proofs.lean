/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
Modifications by Worker 199 with proof-route guidance from Worker 194
(2026-11-13): isolate M110.013 from the pinned source at commit
fbd320cd8b1b06487c58227e92eb135794267709, prefix its namespace by
Langlands.NYLL, and prove the exact published target using the construction's
definitional carrier. Omit the source's unused local HasExtension binding
and the calls to unpublished M110.010/M110.012 proofs.
Retained license and notices: licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension.IntegralClosureValuationSubringStatements

namespace Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation

noncomputable section

universe u v w

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
variable {ΓK : Type w} [LinearOrderedCommGroupWithZero ΓK]

theorem integralClosureValuationSubringOfMemOrInv_isIntegralClosure
    (vK : _root_.Valuation K ΓK)
    (hval :
      ∀ z : L,
        z ∈ (integralClosure vK.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure vK.valuationSubring L).toSubring) :
    integralClosureValuationSubringOfMemOrInv_isIntegralClosureStatement vK hval := by
  let B := integralClosureValuationSubringOfMemOrInv (L := L) vK hval
  change IsIntegralClosure B vK.valuationSubring L
  refine
    { algebraMap_injective := Subtype.coe_injective
      isIntegral_iff := ?_ }
  intro z
  constructor
  · intro hz
    exact ⟨⟨z, hz⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    exact y.2

end

end Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation
