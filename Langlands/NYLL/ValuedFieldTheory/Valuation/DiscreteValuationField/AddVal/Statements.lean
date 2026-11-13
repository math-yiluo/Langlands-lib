/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 296, 2026-11-13: extract the indicated source proposition(s)
from commit fbd320cd8b1b06487c58227e92eb135794267709 as closed Prop-valued
targets; prefix namespaces with Langlands.NYLL and use focused published
imports. Preserve source universes and hypotheses; omit proofs and attributes.
Retain only the required M311.001 compatibility target and import the existing
Library DVR theorem for named reuse rather than re-porting its mathematics.
Retained license and notices: licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupDepth

universe u

namespace Langlands.NYLL.IsDiscreteValuationRing

def mem_maximalIdeal_pow_iff_addVal_geStatement : Prop :=
  ∀ {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (a : R) (n : ℕ),
    a ∈ IsLocalRing.maximalIdeal R ^ n ↔
      (n : ℕ∞) ≤ _root_.IsDiscreteValuationRing.addVal R a

end Langlands.NYLL.IsDiscreteValuationRing
