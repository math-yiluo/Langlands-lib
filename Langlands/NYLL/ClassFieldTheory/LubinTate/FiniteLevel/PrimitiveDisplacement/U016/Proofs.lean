/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 299, 2026-11-13: isolate the M362.016 proof from
commit fbd320cd8b1b06487c58227e92eb135794267709, rename the source-private
helper under Langlands.NYLL.PortInternal.M362, and prove its statement
target. Reduce imports to the target and focused Mathlib tactics.
Retained license and notices: licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveDisplacement.U016.Statements
import Mathlib.Tactic.FinCases

universe u

namespace Langlands.NYLL.PortInternal.M362

theorem d016
    {R : Type u} [CommRing R] [TopologicalSpace R]
    {x y : R} (hx : PowerSeries.HasEval x)
    (hy : PowerSeries.HasEval y) : d016Statement hx hy := by
  unfold d016Statement
  constructor
  · intro i
    fin_cases i
    · exact hx
    · exact hy
  · simp [Filter.cofinite_eq_bot]

end Langlands.NYLL.PortInternal.M362
