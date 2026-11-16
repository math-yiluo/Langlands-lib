/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 793, 2026-11-16: extract the source-private M351.015
theorem (lines 430–435) from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709 as the public theorem
`Langlands.NYLL.PortInternal.M351.d015`, proving its published proposition
target. Refer to the linear model by its published name `d011`; retain
the needed M351.012 calculation (lines 405–413) as a private helper under
a nonconflicting name because the sibling proof is not yet in the Library
base. Replace the source imports with the published statement module,
qualify the opened namespace with Langlands.NYLL, and omit unused source
section settings and the omitted `[Fintype σ]` instance. The original
LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.LinearModel.Statements

/-!
# The linear model has order at least one

The series `d011 π i = C π * X_i` has zero constant coefficient, so its
multivariable order is at least one. This is the adapted proof of M351.015.
-/

universe u v w

namespace Langlands.NYLL.PortInternal.M351

open Langlands.NYLL.LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K}
variable {σ : Type w}

private theorem constantCoeff_linearModel_for_order
    (π : F.valuationSubring) (i : σ) :
    MvPowerSeries.constantCoeff (d011 π i) = 0 := by
  rw [d011, map_mul, MvPowerSeries.constantCoeff_C,
    ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
    MvPowerSeries.coeff_zero_X, mul_zero]

/-- M351.015: the linear model `C π * X_i` has order at least one. -/
theorem d015 (π : F.valuationSubring) (i : σ) : d015Statement π i :=
  MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr
    (constantCoeff_linearModel_for_order π i)

end Langlands.NYLL.PortInternal.M351
