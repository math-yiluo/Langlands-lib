/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 465, 2026-11-15: extract the proof of M349.003
(`map_subst_lubinTateSeries`, source lines 77-92) from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709; prefix the namespace with
Langlands.NYLL; import the published Reduction statement module and the
published M347.004 and M347.005 proof modules in place of the source
imports; state the theorem through its published Prop target
`map_subst_lubinTateSeriesStatement`, unfolded by a leading `show _ = _`;
bind `hH.constantCoeff_eq_zero` and
`hH.hasSubst` with their unfolded types before use; and replace the module
documentation.
The original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Reduction.Statements
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.LinearTerm.U004.Proofs
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.LinearTerm.U005.Proofs

/-!
# Reduction of a Lubin--Tate series evaluated at a series

Proof of NYLL M349.003: for a multivariable series `H` with a prescribed
linear term, reducing `e(H)` to the residue field gives `Hbar ^ q`.
-/

noncomputable section

universe u v w

namespace Langlands.NYLL.LubinTate
namespace SameUniformizer

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}
variable {σ : Type w} [Fintype σ]

/-- The reduced left side `e(H)` is `Hbar ^ q` (NYLL M349.003). -/
theorem map_subst_lubinTateSeries
    (e : LubinTateSeries F π)
    {H : MvPowerSeries σ F.valuationSubring}
    {L : σ → F.valuationSubring} (hH : HasLinearTerm H L) :
    map_subst_lubinTateSeriesStatement e hH := by
  show _ = _
  have hconst : MvPowerSeries.constantCoeff H = 0 :=
    hH.constantCoeff_eq_zero
  have hsubst : PowerSeries.HasSubst H := hH.hasSubst
  have hmap : PowerSeries.HasSubst
      (MvPowerSeries.map F.residueMap H) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by
      simp [hconst])
  rw [PowerSeries.map_subst hsubst e.toPowerSeries,
    e.map_residue_eq_frobenius, PowerSeries.subst_pow hmap,
    PowerSeries.subst_X hmap]

end SameUniformizer
end Langlands.NYLL.LubinTate

end
