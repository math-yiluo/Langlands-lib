/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 490, 2026-11-14: extract the signature of the theorem
M350.004 (lines 77–87) from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709 as the Prop-valued target
`correctionCoefficient_specStatement`; prefix the namespace with
Langlands.NYLL; import the published M350.003 definition module instead of
the source Reduction module; omit the proof and the other source
declarations and replace the module documentation and docstring.
The original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.RecursiveCoefficient.CorrectionCoefficient

/-!
# Target: the defining equation of the recursive correction coefficient

This module states the source theorem `correctionCoefficient_spec`: the
chosen correction coefficient `c` in total degree `d.degree ≥ 2` satisfies
`(1 - π ^ (d.degree - 1)) * c = -normalizedDefectCoefficient …`.
It contains one proposition definition and no proof.
-/

universe u v w

namespace Langlands.NYLL.LubinTate
namespace SameUniformizer

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}
variable {σ : Type w} [Fintype σ]

/-- Target for M350.004: the recursive correction coefficient satisfies its
defining scalar equation. -/
def correctionCoefficient_specStatement
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (e ebar : LubinTateSeries F π)
    {H : MvPowerSeries σ F.valuationSubring}
    {L : σ → F.valuationSubring} (hH : HasLinearTerm H L)
    (d : σ →₀ ℕ) (hd : 2 ≤ d.degree) : Prop :=
  (1 - π ^ (d.degree - 1)) *
      correctionCoefficient hπ e ebar hH d hd =
    -normalizedDefectCoefficient hπ e ebar hH d

end SameUniformizer
end Langlands.NYLL.LubinTate
