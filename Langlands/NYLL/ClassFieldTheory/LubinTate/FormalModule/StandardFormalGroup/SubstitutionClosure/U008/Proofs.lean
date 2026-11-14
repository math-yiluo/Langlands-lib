/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 311, 2026-11-14: extract the proof of M354.008
from upstream commit fbd320cd8b1b06487c58227e92eb135794267709;
prefix its namespace with Langlands.NYLL, import its focused published
statement, and state its result using that exact proposition target.
Preserve the full theorem telescope and the original proof term.
Omit unrelated declarations, unused section settings and source opens.
The original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.StandardFormalGroup.SubstitutionClosure.U008.Statements

/-!
# Mixed power-series substitution

The exact proof of source unit M354.008, using Mathlib's substitution composition.
-/

universe u v w w'

namespace Langlands.NYLL.LubinTate.SameUniformizer

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {σ : Type w} {τ : Type w'}

/-- Multivariable substitution commutes with substituting a multivariable
series into a one-variable power series. -/
theorem subst_powerSeries_subst
    {H : MvPowerSeries σ F.valuationSubring}
    (hH : PowerSeries.HasSubst H)
    {G : σ → MvPowerSeries τ F.valuationSubring}
    (hG : MvPowerSeries.HasSubst G)
    (f : PowerSeries F.valuationSubring) :
    subst_powerSeries_substStatement hH hG f := by
  change
    MvPowerSeries.subst G
        (MvPowerSeries.subst (fun _ : Unit => H) f) =
      MvPowerSeries.subst
        (fun _ : Unit => MvPowerSeries.subst G H) f
  exact MvPowerSeries.subst_comp_subst_apply hH.const hG f

end Langlands.NYLL.LubinTate.SameUniformizer
