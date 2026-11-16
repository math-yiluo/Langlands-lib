/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 695, 2026-11-16: extract only M338.003 (lines 60–71)
from upstream commit fbd320cd8b1b06487c58227e92eb135794267709; prefix
the namespace with Langlands.NYLL; replace the original CoefficientEquation
import by the focused published ToPowerSeriesStatement module; express
the conclusion through that reducible Prop-valued target; and replace
the module documentation. The theorem name, simp attribute, parameters,
uniformizer hypothesis, equation and rfl proof are retained.
The original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.StandardSeries.ToPowerSeriesStatement

/-!
# The underlying series of the standard Lubin--Tate series

The projection of the standard Lubin--Tate series is its defining
polynomial power series `π X + X ^ q`.
-/

noncomputable section

universe u v

namespace Langlands.NYLL.LubinTate

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}

namespace LubinTateSeries

/-- The underlying series of the standard Lubin--Tate input is literally
`π X + X ^ q`. -/
@[simp]
theorem standardLubinTateSeries_toPowerSeries
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) :
    standardLubinTateSeries_toPowerSeriesStatement hπ :=
  rfl

end LubinTateSeries
end Langlands.NYLL.LubinTate

end
