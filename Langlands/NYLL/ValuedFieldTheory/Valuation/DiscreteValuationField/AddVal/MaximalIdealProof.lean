/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 313, 2026-11-13: isolate the cited proof from pinned commit
fbd320cd8b1b06487c58227e92eb135794267709, prefix namespaces with Langlands.NYLL,
and prove the exact closed proposition using focused imports. Changes to the
proof route are recorded in the paired Markdown.
Modified by Worker 289, 2026-11-14: reuse Worker 313's proof draft against the
published target, restore the source docstring, and complete its documentation.
Retained license and notices: licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.AddVal.Statements
import Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupDepth

universe u

namespace Langlands.NYLL.IsDiscreteValuationRing

/-- Membership in a power of the maximal ideal is detected by the normalized
additive valuation. -/
theorem mem_maximalIdeal_pow_iff_addVal_ge :
    mem_maximalIdeal_pow_iff_addVal_geStatement.{u} := by
  intro R _ _ _ a n
  exact _root_.IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_le_addVal
    (R := R) (n := n) (x := a)

end Langlands.NYLL.IsDiscreteValuationRing
