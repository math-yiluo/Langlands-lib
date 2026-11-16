/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 488, 2026-11-14: the proof of the source-private theorem
M351.002 (`truncTotal_powerSeries_subst_eq_of_truncTotal_eq`, source lines
72–107 of Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean,
upstream commit fbd320cd8b1b06487c58227e92eb135794267709), renamed
Langlands.NYLL.PortInternal.M351.d002 and stated against the published target
`d002Statement`; the import is the published statement module together with
Mathlib's multivariable substitution module. The proof script is the
source's, unchanged. The original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.U002.Statements
import Mathlib.RingTheory.MvPowerSeries.Substitution

/-!
# Truncation of `e(H)` depends only on the truncation of `H`: proof

Proof of M351.002 (source-private): for `H`, `H'` with zero constant
coefficient and equal total-degree truncation at `k`, the composites
`e(H)` and `e(H')` have equal total-degree truncation at `k`.
-/

attribute [local instance] Classical.propDecidable

universe u v w

namespace Langlands.NYLL.PortInternal.M351

open Langlands.NYLL.LocalFieldTheory.DiscreteValuationField
open Langlands.NYLL.LubinTate
open Langlands.NYLL.LubinTate.SameUniformizer

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}
variable {σ : Type w}

/-- M351.002: truncation at `k` of `e(H)` depends only on the truncation at
`k` of `H`, for `H` with zero constant coefficient. -/
theorem d002 [Finite σ]
    (e : LubinTateSeries F π)
    {H H' : MvPowerSeries σ F.valuationSubring}
    (hH : MvPowerSeries.constantCoeff H = 0)
    (hH' : MvPowerSeries.constantCoeff H' = 0)
    {k : ℕ} (htrunc : H.truncTotal k = H'.truncTotal k) :
    d002Statement e hH hH' htrunc := by
  have hHsubst : PowerSeries.HasSubst H :=
    PowerSeries.HasSubst.of_constantCoeff_zero hH
  have hH'subst : PowerSeries.HasSubst H' :=
    PowerSeries.HasSubst.of_constantCoeff_zero hH'
  change
    (MvPowerSeries.subst (fun _ : Unit ↦ H) e.toPowerSeries).truncTotal k =
      (MvPowerSeries.subst (fun _ : Unit ↦ H') e.toPowerSeries).truncTotal k
  calc
    (MvPowerSeries.subst (fun _ : Unit ↦ H) e.toPowerSeries).truncTotal k =
        (MvPowerSeries.subst
          (fun _ : Unit ↦ (H.truncTotal k).toMvPowerSeries)
          e.toPowerSeries).truncTotal k := by
      exact
        MvPowerSeries.truncTotal_subst_eq_truncTotal_subst_truncTotal_of_le
          (f := e.toPowerSeries) (a := fun _ : Unit ↦ H)
          (x := fun _ : Unit ↦ k) hHsubst.const (fun _ ↦ le_rfl)
    _ = (MvPowerSeries.subst
          (fun _ : Unit ↦ (H'.truncTotal k).toMvPowerSeries)
          e.toPowerSeries).truncTotal k := by
      rw [htrunc]
    _ = (MvPowerSeries.subst (fun _ : Unit ↦ H')
          e.toPowerSeries).truncTotal k := by
      exact
        (MvPowerSeries.truncTotal_subst_eq_truncTotal_subst_truncTotal_of_le
          (f := e.toPowerSeries) (a := fun _ : Unit ↦ H')
          (x := fun _ : Unit ↦ k) hH'subst.const
          (fun _ ↦ le_rfl)).symm

end Langlands.NYLL.PortInternal.M351
