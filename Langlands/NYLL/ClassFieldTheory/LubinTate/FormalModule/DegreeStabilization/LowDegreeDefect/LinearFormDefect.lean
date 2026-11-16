/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 713, 2026-11-16: extract M351.029 (source lines
890-897) from upstream commit fbd320cd8b1b06487c58227e92eb135794267709.
Rename the source-private theorem to Langlands.NYLL.PortInternal.M351.d029,
state its conclusion through the published d029Statement, and replace the
source imports by the focused statement and prerequisite proof modules.
Use the published d027 and d028 names in the original rewrite/apply route;
the finite sum over Finset.univ is definitionally the required full sum.
Omit unused ambient noncomputability, big-operator scope and classical
decidability commands. The original LICENSE and NOTICE remain in
licenses/NYLL/. The paired Markdown records the source and adaptations.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.LowDegreeDefect.Statements
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.LowDegreeDefect.LinearFormMonomialSum
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.LowDegreeDefect.SumLinearMonomialsDefect

/-!
# The defect of a linear form vanishes through degree one

Rewrite a linear form as the sum of its degree-one monomials, then apply
the finite-sum defect theorem to the full variable set.
-/

universe u v w

namespace Langlands.NYLL

open LubinTate LubinTate.SameUniformizer
open LocalFieldTheory.DiscreteValuationField

namespace PortInternal.M351

/-- The same-uniformizer defect of a linear form has no constant or
linear coefficient. -/
theorem d029 {K : Type u} [Field K]
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    {σ : Type w} [Fintype σ]
    (e ebar : LubinTateSeries F π)
    (L : σ → F.valuationSubring)
    (q : σ →₀ ℕ) (hq : q.degree ≤ 1) :
    d029Statement e ebar L q hq := by
  rw [d029Statement, d027 L]
  exact d028 e ebar L Finset.univ q hq

end PortInternal.M351

end Langlands.NYLL
