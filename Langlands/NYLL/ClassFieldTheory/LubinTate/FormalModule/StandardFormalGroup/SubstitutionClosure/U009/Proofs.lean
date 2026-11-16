/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 228, 2026-11-16: extract the proof of M354.009
from upstream commit fbd320cd8b1b06487c58227e92eb135794267709;
prefix the namespace with Langlands.NYLL, import its focused published
statement and M354.008 proof, and express the conclusion using the exact
published proposition target. Preserve the full source telescope and
the original three-step proof after exposing the target with change.
Omit unrelated declarations, unused source
opens and section settings, and focus the module documentation.
The original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.StandardFormalGroup.SubstitutionClosure.U009.Statements
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.StandardFormalGroup.SubstitutionClosure.U008.Proofs

/-!
# Substitution into an inserted variable

The exact proof of source unit M354.009, using mixed substitution and
Mathlib's substitution law for a variable.
-/

universe u v w w'

namespace Langlands.NYLL.LubinTate.SameUniformizer

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}
variable {σ : Type w} {τ : Type w'}

/-- Substituting a family into `e(X_i)` evaluates `e` at that family's
corresponding member. -/
theorem subst_inVariable
    (e : LubinTateSeries F π)
    {G : σ → MvPowerSeries τ F.valuationSubring}
    (hG : MvPowerSeries.HasSubst G) (i : σ) :
    subst_inVariableStatement e hG i := by
  change MvPowerSeries.subst G (inVariable e i) =
    PowerSeries.subst (G i) e.toPowerSeries
  rw [inVariable]
  rw [subst_powerSeries_subst (PowerSeries.HasSubst.X i) hG]
  simp [MvPowerSeries.subst_X hG]

end Langlands.NYLL.LubinTate.SameUniformizer
