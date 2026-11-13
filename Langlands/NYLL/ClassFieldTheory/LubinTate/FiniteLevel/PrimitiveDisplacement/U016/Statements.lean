/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 299, 2026-11-13: extract the proposition of M362.016
from commit fbd320cd8b1b06487c58227e92eb135794267709, rename the private
helper in Langlands.NYLL.PortInternal.M362, and replace the theorem
with its Prop-valued statement target. Reduce imports to Mathlib.
Retained license and notices: licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Mathlib.RingTheory.PowerSeries.Evaluation

/-! # Evaluation admissibility for a pair of points -/

universe u

namespace Langlands.NYLL.PortInternal.M362

/-- NYLL M362.016: two individually admissible points form an admissible
pair for bivariate power-series evaluation. -/
def d016Statement
    {R : Type u} [CommRing R] [TopologicalSpace R]
    {x y : R} (_hx : PowerSeries.HasEval x)
    (_hy : PowerSeries.HasEval y) : Prop :=
  MvPowerSeries.HasEval (![x, y] : Fin 2 → R)

end Langlands.NYLL.PortInternal.M362
