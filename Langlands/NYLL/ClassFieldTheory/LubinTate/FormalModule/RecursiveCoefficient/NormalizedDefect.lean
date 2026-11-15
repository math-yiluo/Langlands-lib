/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 490, 2026-11-14: extract only the definition M350.001
(lines 34–43) from upstream commit fbd320cd8b1b06487c58227e92eb135794267709;
prefix the namespace with Langlands.NYLL, replace the source Reduction import
by the published module of the exact M349.006 proof, omit the other four
source declarations (published separately) and replace the module
documentation. The declaration docstring, binders, type and body are
unchanged. The original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Reduction.UniformizerDvdCoeffDefect

/-!
# Normalized defect coefficients

Every coefficient of a same-uniformizer intertwining defect is divisible by
the chosen uniformizer `π`. This module chooses the quotient.
-/

noncomputable section

universe u v w

namespace Langlands.NYLL.LubinTate
namespace SameUniformizer

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}
variable {σ : Type w} [Fintype σ]

/-- The coefficient of an intertwining defect after removing one factor of
the chosen uniformizer. -/
noncomputable def normalizedDefectCoefficient
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (e ebar : LubinTateSeries F π)
    {H : MvPowerSeries σ F.valuationSubring}
    {L : σ → F.valuationSubring} (hH : HasLinearTerm H L)
    (d : σ →₀ ℕ) :
    F.valuationSubring :=
  Classical.choose (uniformizer_dvd_coeff_defect hπ e ebar hH d)

end SameUniformizer
end Langlands.NYLL.LubinTate

end
