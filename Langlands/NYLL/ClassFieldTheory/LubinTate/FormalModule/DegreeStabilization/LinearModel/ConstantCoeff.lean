/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 790, 2026-11-16: extract the source-private theorem
M351.012 (`linearInVariableStabilization_constantCoeff`, lines 405–413)
from upstream commit fbd320cd8b1b06487c58227e92eb135794267709; publish
it as `Langlands.NYLL.PortInternal.M351.d012` with result type the
published `d012Statement`; use the published linear model `d011`;
replace the source imports by the published statement module; omit
the unused section instance `[Fintype σ]` and its `omit` command,
the unused local decidability instance, and unrelated declarations.
The source rewrite proof is retained after exposing the target.
The original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.LinearModel.Statements

/-!
# The linear model has zero constant coefficient

Proof of M351.012: the multivariable series `d011 π i = C π * X_i`
has zero constant coefficient.
-/

universe u v w

namespace Langlands.NYLL.PortInternal.M351

open Langlands.NYLL.LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K}
variable {σ : Type w}

/-- M351.012 (source-private `linearInVariableStabilization_constantCoeff`):
the linear model `C π * X_i` has zero constant coefficient. -/
theorem d012 (π : F.valuationSubring) (i : σ) : d012Statement π i := by
  show MvPowerSeries.constantCoeff (d011 π i) = 0
  rw [d011, map_mul, MvPowerSeries.constantCoeff_C,
    ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
    MvPowerSeries.coeff_zero_X, mul_zero]

end Langlands.NYLL.PortInternal.M351
