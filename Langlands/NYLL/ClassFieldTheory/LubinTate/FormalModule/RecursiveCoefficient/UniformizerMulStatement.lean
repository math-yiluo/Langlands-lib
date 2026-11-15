/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 490, 2026-11-14: extract the signature of the theorem
M350.002 (lines 45–54) from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709 as the Prop-valued target
`uniformizer_mul_normalizedDefectCoefficientStatement`; prefix the namespace
with Langlands.NYLL; import the published M350.001 definition module instead
of the source Reduction module; omit the proof and the other source
declarations and replace the module documentation and docstring.
The original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.RecursiveCoefficient.NormalizedDefect

/-!
# Target: the normalized defect coefficient times the uniformizer

This module states the source theorem
`uniformizer_mul_normalizedDefectCoefficient`: multiplying the chosen
normalized defect coefficient by `π` recovers the defect coefficient.
It contains one proposition definition and no proof.
-/

universe u v w

namespace Langlands.NYLL.LubinTate
namespace SameUniformizer

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}
variable {σ : Type w} [Fintype σ]

/-- Target for M350.002: multiplying the normalized defect coefficient by the
uniformizer recovers the original coefficient of the defect. -/
def uniformizer_mul_normalizedDefectCoefficientStatement
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (e ebar : LubinTateSeries F π)
    {H : MvPowerSeries σ F.valuationSubring}
    {L : σ → F.valuationSubring} (hH : HasLinearTerm H L)
    (d : σ →₀ ℕ) : Prop :=
  π * normalizedDefectCoefficient hπ e ebar hH d =
    MvPowerSeries.coeff d (defect e ebar H)

end SameUniformizer
end Langlands.NYLL.LubinTate
