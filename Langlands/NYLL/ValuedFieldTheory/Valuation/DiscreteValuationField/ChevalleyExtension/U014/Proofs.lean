/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
Modifications by Worker 199 with proof-route guidance from Worker 194
(2026-11-13): isolate M110.014 from the pinned source at commit
fbd320cd8b1b06487c58227e92eb135794267709, prefix its namespace by
Langlands.NYLL, and prove the exact published proposition target directly
using Mathlib instead of importing the unpublished M110.007/M110.010 proofs.
Retained license and notices: licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension.IntegralClosureValuationSubringStatements
import Mathlib.RingTheory.Valuation.Integral

namespace Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation

noncomputable section

universe u v w x

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
variable {ΓK : Type w} [LinearOrderedCommGroupWithZero ΓK]

theorem integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension
    {ΓL : Type x} [LinearOrderedCommGroupWithZero ΓL]
    (vK : _root_.Valuation K ΓK) (vL : _root_.Valuation L ΓL)
    (hval :
      ∀ z : L,
        z ∈ (integralClosure vK.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure vK.valuationSubring L).toSubring)
    [vK.HasExtension vL] :
    integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtensionStatement
      vK vL hval := by
  intro z hz
  have hz_base : IsIntegral vK.valuationSubring z := hz
  have hz_target : IsIntegral vL.valuationSubring z :=
    IsIntegral.tower_top (A := vL.valuationSubring) hz_base
  exact _root_.Valuation.Integers.mem_of_integral
    (_root_.Valuation.valuationSubring.integers (v := vL)) hz_target

end

end Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation
