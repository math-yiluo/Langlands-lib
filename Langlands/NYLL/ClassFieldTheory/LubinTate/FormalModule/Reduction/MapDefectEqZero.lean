/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 465, 2026-11-15: extract the proof of M349.005
(`map_defect_eq_zero`, source lines 110-119) from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709; prefix the namespace with
Langlands.NYLL; import the published Reduction statement module and the
published M349.001, M349.003 and M349.004 proof modules in place of the
source imports; state the theorem through its published Prop target
`map_defect_eq_zeroStatement`, unfolded by a leading `show _ = _`; and
replace the module documentation. The original LICENSE and NOTICE remain in
licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Reduction.Statements
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Reduction.ExpandNatCard
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Reduction.MapSubstLubinTateSeries
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Reduction.MapSubstInVariables

/-!
# Reduction of a same-uniformizer intertwining defect

Proof of NYLL M349.005: the defect `e(H) - H(ebar(X_i))_i` of two
Lubin--Tate series with the same linear coefficient reduces to zero in the
residue field.
-/

noncomputable section

universe u v w

namespace Langlands.NYLL.LubinTate
namespace SameUniformizer

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}
variable {σ : Type w} [Fintype σ]

/-- The same-uniformizer intertwining defect vanishes after reduction
(NYLL M349.005). -/
theorem map_defect_eq_zero
    (e ebar : LubinTateSeries F π)
    {H : MvPowerSeries σ F.valuationSubring}
    {L : σ → F.valuationSubring} (hH : HasLinearTerm H L) :
    map_defect_eq_zeroStatement e ebar hH := by
  show _ = _
  rw [defect, map_sub, map_subst_lubinTateSeries e hH,
    map_subst_inVariables ebar H,
    mvPowerSeries_expand_natCard]
  exact sub_self _

end SameUniformizer
end Langlands.NYLL.LubinTate

end
