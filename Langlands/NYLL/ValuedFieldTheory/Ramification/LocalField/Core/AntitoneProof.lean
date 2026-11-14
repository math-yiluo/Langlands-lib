/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 296, 2026-11-13: extract M327.010 from pinned NYLL
commit fbd320cd8b1b06487c58227e92eb135794267709, prefix namespaces,
prove the closed proposition target and replace the global extension
instance by the chosenLocalExtension_properties local witness.
Prepared by Worker 314, 2026-11-14: reuse Worker 296's proof unchanged
for the focused exact-proof task and expand its paired documentation.
Retained license and notices: licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.LocalField.Core.AntitoneStatement
import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.HerbrandFunction.LawsProof

namespace Langlands.NYLL.RamificationTheory.LocalField

open Langlands.NYLL.LocalFieldTheory
open Langlands.NYLL.RamificationTheory.HilbertRamification

/-- The local upper ramification filtration is antitone. -/
theorem localUpperRamificationGroup_antitone :
    localUpperRamificationGroup_antitoneStatement := by
  intro K L _ _ _ _ _ _ _ _ s t hst
  let : _root_.Valuation.HasExtension (localCompleteDVF K).valuation
      (chosenLocalExtensionCompleteDVF K L).valuation :=
    Classical.choose (chosenLocalExtension_properties K L)
  unfold localUpperRamificationGroup
  apply Higher.lowerRamificationGroup_antitone
    (chosenLocalExtension_uniqueValuationExtension.{0} K L)
  exact
    (Higher.inverseHerbrandFunctionOfUniqueExtension_strictMono
      (chosenLocalExtension_uniqueValuationExtension.{0} K L)).monotone hst

end Langlands.NYLL.RamificationTheory.LocalField
