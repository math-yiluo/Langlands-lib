/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 296, 2026-11-13: extract the indicated source proposition(s)
from commit fbd320cd8b1b06487c58227e92eb135794267709 as closed Prop-valued
targets; prefix namespaces with Langlands.NYLL and use focused published
imports. Preserve source universes and hypotheses; omit proofs and attributes.
Retained license and notices: licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.LocalField.Core.Definitions
import Langlands.NYLL.ValuedFieldTheory.Ramification.GaloisValuation.IntermediateFieldRestriction.Definitions

namespace Langlands.NYLL.RamificationTheory.LocalField

open Langlands.NYLL.LocalFieldTheory

def localUpperRamificationGroup_map_restrictStatement : Prop :=
  ∀ (K : Type) [Field K]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (E F : IntermediateField K (SeparableClosure K)) (hEF : E ≤ F)
    [FiniteDimensional K E] [FiniteDimensional K F]
    [IsGalois K E] [IsGalois K F]
    (t : ℝ),
    Subgroup.map
        (Langlands.NYLL.RamificationTheory.intermediateFieldRestrictNormalHom E F hEF)
        (localUpperRamificationGroup K F t) =
      localUpperRamificationGroup K E t

end Langlands.NYLL.RamificationTheory.LocalField
