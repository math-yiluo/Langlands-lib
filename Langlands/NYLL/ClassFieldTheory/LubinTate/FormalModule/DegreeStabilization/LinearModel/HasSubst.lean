/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 791, 2026-11-16: extract M351.013 (source lines
415–421) from upstream commit fbd320cd8b1b06487c58227e92eb135794267709;
publish the source-private theorem as Langlands.NYLL.PortInternal.M351.d013,
using its published target with explicit σ and the published linear model
d011. Import the focused Statements module. Prove the M351.012
constant-coefficient prerequisite privately under a fresh name, retaining
its source proof (lines 405–413). Omit unused source section settings,
adapt documentation, and retain the original LICENSE and NOTICE in
licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.LinearModel.Statements

/-!
# Substitution by the linear model

Proof of NYLL M351.013, with its elementary constant-coefficient prerequisite
proved privately.
-/

universe u v w

namespace Langlands.NYLL.PortInternal.M351

open Langlands.NYLL.LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K}
variable {σ : Type w}

private theorem constantCoeff_linearModel_for_subst
    (π : F.valuationSubring) (i : σ) :
    MvPowerSeries.constantCoeff (d011 π i) = 0 := by
  rw [d011, map_mul,
    MvPowerSeries.constantCoeff_C,
    ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
    MvPowerSeries.coeff_zero_X, mul_zero]

/-- The linear model `i ↦ C π * X_i` admits substitution for finite `σ`
(NYLL M351.013). -/
theorem d013 [Finite σ] (π : F.valuationSubring) :
    d013Statement (σ := σ) π :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero
    (constantCoeff_linearModel_for_subst π)

end Langlands.NYLL.PortInternal.M351
