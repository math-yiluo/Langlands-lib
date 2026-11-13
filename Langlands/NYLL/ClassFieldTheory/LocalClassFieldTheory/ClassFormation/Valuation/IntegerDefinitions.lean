/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 230, 13 November 2026: extract M140.003, .004 and .007
from commit fbd320cd8b1b06487c58227e92eb135794267709, prefix the namespace
with Langlands.NYLL, and import published dependencies. The theorem targets
are Prop-valued definitions with the Statement suffix. Data construction
bodies and local action scope are preserved. See the paired Markdown;
LICENSE and NOTICE are retained under licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.GaloisIntegerRing.Actions
import Mathlib.Algebra.Group.Action.Units

namespace Langlands.NYLL.LocalClassFieldTheory

open Langlands.NYLL.LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

/-- The action on integer units induced by integral-closure restriction. -/
@[implicit_reducible]
def galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    MulDistribMulAction (Gal(L / K)) 𝒪[L]ˣ := by
  let hIntegerAction : MulSemiringAction (Gal(L / K)) 𝒪[L] :=
    galoisGroupIntegerRingMulSemiringActionOfIsIntegralClosure K L
  exact Units.mulDistribMulActionRight

end
end Langlands.NYLL.LocalClassFieldTheory
