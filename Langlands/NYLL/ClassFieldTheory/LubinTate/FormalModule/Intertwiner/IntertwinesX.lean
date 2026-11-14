/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 334, 2026-11-14: extract M348.007 from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709, import the published focused
statement module, prefix the namespace with Langlands.NYLL, and express the
theorem type through its published target, unfolded explicitly in the proof.
Prove the M348.002 and M348.003 prerequisites privately under fresh names
so this focused candidate needs no proof still awaiting publication.
The original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Intertwiner.Statements

/-!
# Each coordinate intertwines a Lubin--Tate series with itself

Proof of the published M348.007 target, with private proofs of its elementary
substitution prerequisites.
-/

noncomputable section

universe u v

namespace Langlands.NYLL.LubinTate
namespace SameUniformizer

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}
variable {σ : Type*}

private theorem constantCoeff_inVariable_for_coordinate
    (e : LubinTateSeries F π) (i : σ) :
    MvPowerSeries.constantCoeff (inVariable e i) = 0 := by
  exact PowerSeries.constantCoeff_subst_eq_zero
    (MvPowerSeries.constantCoeff_X (R := F.valuationSubring) i)
    e.toPowerSeries e.constantCoeff_eq_zero

private theorem inVariable_hasSubst_for_coordinate [Finite σ]
    (e : LubinTateSeries F π) :
    MvPowerSeries.HasSubst (fun i : σ ↦ inVariable e i) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero
    (fun i ↦ constantCoeff_inVariable_for_coordinate e i)

/-- Each coordinate intertwines `e` with itself when `σ` is finite
(NYLL M348.007). -/
theorem intertwines_X [Finite σ] (e : LubinTateSeries F π) (i : σ) :
    intertwines_XStatement e i := by
  rw [intertwines_XStatement, Intertwines,
    MvPowerSeries.subst_X (inVariable_hasSubst_for_coordinate e)]
  rfl

end SameUniformizer
end Langlands.NYLL.LubinTate

end
