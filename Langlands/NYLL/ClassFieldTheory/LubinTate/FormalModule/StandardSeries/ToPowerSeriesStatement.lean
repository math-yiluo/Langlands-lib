/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 410, 2026-11-14: state only the proposition of M338.003
(lines 60–69) from upstream commit fbd320cd8b1b06487c58227e92eb135794267709
as the Prop-valued target standardLubinTateSeries_toPowerSeriesStatement;
the theorem, its simp attribute and its rfl proof belong to the separate
proof successor. Prefix the namespace with Langlands.NYLL, replace the
original CoefficientEquation import by the focused published module of
standardLubinTateSeries, and replace the module documentation. The
parameters, hypothesis and equation are unchanged.
The original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.StandardSeries.Definitions

/-!
# Target: the underlying series of the standard Lubin--Tate series

The Prop-valued target of source theorem
`LubinTate.LubinTateSeries.standardLubinTateSeries_toPowerSeries`.
-/

noncomputable section

universe u v

namespace Langlands.NYLL.LubinTate

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}

namespace LubinTateSeries

/-- Target: the underlying series of the standard Lubin--Tate input is
literally `π X + X ^ q`. -/
abbrev standardLubinTateSeries_toPowerSeriesStatement
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) : Prop :=
  (standardLubinTateSeries hπ).toPowerSeries =
    standardLubinTatePowerSeries F π

end LubinTateSeries
end Langlands.NYLL.LubinTate

end
