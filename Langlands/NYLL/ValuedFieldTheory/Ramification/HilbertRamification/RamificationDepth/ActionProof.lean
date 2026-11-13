/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 313, 2026-11-13: isolate the cited proof from pinned commit
fbd320cd8b1b06487c58227e92eb135794267709, prefix namespaces with Langlands.NYLL,
and prove the exact closed proposition using focused imports. Changes to the
proof route are recorded in the paired Markdown.
Retained license and notices: licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.RamificationDepth.ActionStatement
import Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupDepth

universe u v w x

namespace Langlands.NYLL.RamificationTheory.HilbertRamification.Higher

theorem addVal_valuationSubringAutOfUniqueExtension :
    addVal_valuationSubringAutOfUniqueExtensionStatement.{u, v, w, x} := by
  intro K L _ _ _ base target _ huniq sigma a
  exact _root_.IsDiscreteValuationRing.addVal_smul
    (valuationSubringAutOfUniqueExtension (base := base) (target := target) huniq sigma) a

end Langlands.NYLL.RamificationTheory.HilbertRamification.Higher
