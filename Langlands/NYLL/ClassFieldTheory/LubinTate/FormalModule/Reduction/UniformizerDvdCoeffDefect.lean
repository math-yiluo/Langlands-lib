/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 465, 2026-11-15: extract the proof of M349.006
(`uniformizer_dvd_coeff_defect`, source lines 121-133) from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709; prefix the namespace with
Langlands.NYLL; import the published Reduction statement module and the
published M349.001, M349.003, M349.004 and M337.002 proof modules in place
of the source imports; state the theorem through its published Prop target
`uniformizer_dvd_coeff_defectStatement`, unfolded by a leading
`show _ ∣ _`; prove the M349.005 prerequisite privately under a fresh name
(repeating its source proof, lines 116-119) so that this focused candidate
does not import a proof still awaiting publication; and replace the module
documentation. The original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Reduction.Statements
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Reduction.ExpandNatCard
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Reduction.MapSubstLubinTateSeries
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Reduction.MapSubstInVariables
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.CoefficientEquation.U002.Proofs

/-!
# Uniformizer divisibility of the intertwining defect

Proof of NYLL M349.006: when the chosen element `π` is a uniformizer, every
coefficient of the same-uniformizer intertwining defect is divisible by `π`.
-/

noncomputable section

universe u v w

namespace Langlands.NYLL.LubinTate
namespace SameUniformizer

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}
variable {σ : Type w} [Fintype σ]

/-- The same-uniformizer intertwining defect vanishes after reduction; a
private copy of the source proof of M349.005. -/
private theorem map_defect_eq_zero_for_dvd
    (e ebar : LubinTateSeries F π)
    {H : MvPowerSeries σ F.valuationSubring}
    {L : σ → F.valuationSubring} (hH : HasLinearTerm H L) :
    MvPowerSeries.map F.residueMap (defect e ebar H) = 0 := by
  rw [defect, map_sub, map_subst_lubinTateSeries e hH,
    map_subst_inVariables ebar H,
    mvPowerSeries_expand_natCard]
  exact sub_self _

/-- Every coefficient of the defect is divisible by the chosen
uniformizer (NYLL M349.006). -/
theorem uniformizer_dvd_coeff_defect
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (e ebar : LubinTateSeries F π)
    {H : MvPowerSeries σ F.valuationSubring}
    {L : σ → F.valuationSubring} (hH : HasLinearTerm H L)
    (d : σ →₀ ℕ) :
    uniformizer_dvd_coeff_defectStatement hπ e ebar hH d := by
  show _ ∣ _
  apply uniformizer_dvd_of_residueMap_eq_zero hπ
  have hcoeff := congrArg (MvPowerSeries.coeff d)
    (map_defect_eq_zero_for_dvd e ebar hH)
  simpa using hcoeff

end SameUniformizer
end Langlands.NYLL.LubinTate

end
