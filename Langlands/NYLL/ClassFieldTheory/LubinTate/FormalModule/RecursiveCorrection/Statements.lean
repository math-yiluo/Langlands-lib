/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 496, 2026-11-14: extract the signatures of M352.003
and M352.004 (lines 56–64 and 83–93) from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709; prefix the namespace with
Langlands.NYLL, append `Statement` to both theorem names and replace each
theorem and proof by a Prop-valued definition with the same parameters
and conclusion. Reuse the published monomialCorrection and
correctedIntertwiner definitions, the published defect definition and the
published HasLinearTerm predicate instead of the source imports
RecursiveCoefficient and DegreeStabilization. Omit the unused
`noncomputable section` and `open scoped BigOperators`, and replace the
module documentation. The original LICENSE and NOTICE remain in
licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.RecursiveCorrection.Definitions
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Intertwiner.Definitions

/-!
# Targets for recursive monomial corrections

Inserting the selected correction monomial in total degree at least two
preserves the prescribed linear term, and cancels the coefficient of the
intertwining defect in exactly the inserted multidegree `d`.
-/

universe u v w

namespace Langlands.NYLL.LubinTate
namespace SameUniformizer

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}
variable {σ : Type w} [Fintype σ]

/-- Target: a correction in total degree at least two does not change the
prescribed linear term. -/
def correctedIntertwiner_hasLinearTermStatement
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (e ebar : LubinTateSeries F π)
    {H : MvPowerSeries σ F.valuationSubring}
    {L : σ → F.valuationSubring} (hH : HasLinearTerm H L)
    (d : σ →₀ ℕ) (hd : 2 ≤ d.degree) : Prop :=
  HasLinearTerm (correctedIntertwiner hπ e ebar hH d hd) L

/-- Target: the recursively selected degree-`d` monomial cancels the
degree-`d` coefficient of the intertwining defect. -/
def coeff_defect_correctedIntertwiner_eq_zeroStatement
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (e ebar : LubinTateSeries F π)
    {H : MvPowerSeries σ F.valuationSubring}
    {L : σ → F.valuationSubring} (hH : HasLinearTerm H L)
    (d : σ →₀ ℕ) (hd : 2 ≤ d.degree) : Prop :=
  MvPowerSeries.coeff d
      (defect e ebar
        (correctedIntertwiner hπ e ebar hH d hd)) = 0

end SameUniformizer
end Langlands.NYLL.LubinTate
