/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 496, 2026-11-14: extract only the definitions M352.001
and M352.002 (lines 35–54) from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709; prefix the namespace with
Langlands.NYLL, replace the source imports RecursiveCoefficient and
DegreeStabilization by the published focused correction-coefficient
module, omit the two source theorems (published separately as Prop
targets and proofs) and the unused `open scoped BigOperators`, and replace
the module documentation. Both definition bodies and types are unchanged.
The original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.RecursiveCoefficient.CorrectionCoefficient

/-!
# Recursive monomial corrections for Lubin--Tate intertwiners

One step of the recursive same-uniformizer intertwiner construction inserts
the selected correction coefficient in multidegree `d` as a single monomial
and adds it to the current approximation `H`.
-/

noncomputable section

universe u v w

namespace Langlands.NYLL.LubinTate
namespace SameUniformizer

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}
variable {σ : Type w} [Fintype σ]

/-- The single monomial inserted at one step of the recursive construction. -/
noncomputable def monomialCorrection
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (e ebar : LubinTateSeries F π)
    {H : MvPowerSeries σ F.valuationSubring}
    {L : σ → F.valuationSubring} (hH : HasLinearTerm H L)
    (d : σ →₀ ℕ) (hd : 2 ≤ d.degree) :
    MvPowerSeries σ F.valuationSubring :=
  MvPowerSeries.monomial d
    (correctionCoefficient hπ e ebar hH d hd)

/-- Insert the recursive correction into the current approximation. -/
noncomputable def correctedIntertwiner
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (e ebar : LubinTateSeries F π)
    {H : MvPowerSeries σ F.valuationSubring}
    {L : σ → F.valuationSubring} (hH : HasLinearTerm H L)
    (d : σ →₀ ℕ) (hd : 2 ≤ d.degree) :
    MvPowerSeries σ F.valuationSubring :=
  H + monomialCorrection hπ e ebar hH d hd

end SameUniformizer
end Langlands.NYLL.LubinTate

end
