/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
Modifications by Worker 194 (2026-11-13): extract focused M110 units from
Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/ChevalleyExtension.lean
at commit fbd320cd8b1b06487c58227e92eb135794267709 into Langlands.NYLL;
replace upstream imports by focused Mathlib imports and the local definition
module where needed. Retain the source construction and statement telescopes;
convert the selected theorem conclusions to Prop-valued definitions without
publishing their proofs. In M110.013 only, zeta-erase the unused local
HasExtension proof binding in the conclusion. See the paired Markdown for
the exact per-file source correspondence. Retained license and notices:
licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Valuation.ValuationSubring

/-! The actual integral closure, supplied with its valuative dichotomy, as a
valuation subring of the extension field (NYLL M110.009). -/

namespace Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation

noncomputable section

universe u v w x y z

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
variable {ΓK : Type w} [LinearOrderedCommGroupWithZero ΓK]

def integralClosureValuationSubringOfMemOrInv
    (vK : _root_.Valuation K ΓK)
    (hval :
      ∀ z : L,
        z ∈ (integralClosure vK.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure vK.valuationSubring L).toSubring) :
    ValuationSubring L :=
  ValuationSubring.ofSubring
    (integralClosure vK.valuationSubring L).toSubring hval

end

end Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation
