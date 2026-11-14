/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 334, 2026-11-14: extract M348.003 from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709, import the published focused
statement module, prefix the namespace with Langlands.NYLL, and express the
theorem type through its published target, naming the variable type.
Prove the M348.002 prerequisite privately under a fresh name so this focused
candidate does not import a proof still awaiting publication.
The original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Intertwiner.Statements

/-!
# Substitution by the inserted Lubin--Tate series

Proof of the published M348.003 target, with a private proof of its elementary
zero-constant-coefficient prerequisite.
-/

noncomputable section

universe u v

namespace Langlands.NYLL.LubinTate
namespace SameUniformizer

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}
variable {σ : Type*}

private theorem constantCoeff_inVariable_for_subst
    (e : LubinTateSeries F π) (i : σ) :
    MvPowerSeries.constantCoeff (inVariable e i) = 0 := by
  exact PowerSeries.constantCoeff_subst_eq_zero
    (MvPowerSeries.constantCoeff_X (R := F.valuationSubring) i)
    e.toPowerSeries e.constantCoeff_eq_zero

/-- The family `i ↦ e(X_i)` admits substitution when `σ` is finite
(NYLL M348.003). -/
theorem inVariable_hasSubst [Finite σ] (e : LubinTateSeries F π) :
    inVariable_hasSubstStatement (σ := σ) e :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero
    (fun i ↦ constantCoeff_inVariable_for_subst e i)

end SameUniformizer
end Langlands.NYLL.LubinTate

end
