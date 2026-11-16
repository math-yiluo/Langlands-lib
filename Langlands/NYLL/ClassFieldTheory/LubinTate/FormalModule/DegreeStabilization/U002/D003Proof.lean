/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 488, 2026-11-14: the proof of the source-private theorem
M351.003 (`truncTotal_inVariables_subst_eq_of_truncTotal_eq`, source lines
109–133 of Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean,
upstream commit fbd320cd8b1b06487c58227e92eb135794267709), renamed
Langlands.NYLL.PortInternal.M351.d003 and stated against the published target
`d003Statement`; the import is the published statement module together with
Mathlib's multivariable substitution module. The source obtains the zero
constant coefficient of `inVariable ebar i` from `constantCoeff_inVariable`
(M348.002); here it is computed directly with Mathlib's
`PowerSeries.constantCoeff_subst_eq_zero`. The rest of the proof script is
the source's, unchanged. The original LICENSE and NOTICE remain in
licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.U002.Statements
import Mathlib.RingTheory.MvPowerSeries.Substitution

/-!
# Truncation of `H(ebar(X_i))_i` depends only on the truncation of `H`: proof

Proof of M351.003 (source-private): for `H`, `H'` with equal total-degree
truncation at `k`, the substitutions `H(ebar(X_i))_i` and
`H'(ebar(X_i))_i` have equal total-degree truncation at `k`.
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

/-- M351.003: truncation at `k` of `H(ebar(X_i))_i` depends only on the
truncation at `k` of `H`. -/
theorem d003 [Finite σ]
    (ebar : LubinTateSeries F π)
    {H H' : MvPowerSeries σ F.valuationSubring}
    {k : ℕ} (htrunc : H.truncTotal k = H'.truncTotal k) :
    d003Statement ebar htrunc := by
  have hconstant :
      ∀ i : σ,
        MvPowerSeries.constantCoeff (inVariable ebar i) = 0 := by
    intro i
    exact PowerSeries.constantCoeff_subst_eq_zero
      (MvPowerSeries.constantCoeff_X i) ebar.toPowerSeries
      ebar.constantCoeff_eq_zero
  calc
    (MvPowerSeries.subst (fun i : σ ↦ inVariable ebar i) H).truncTotal k =
        (MvPowerSeries.subst (fun i : σ ↦ inVariable ebar i)
          (H.truncTotal k).toMvPowerSeries).truncTotal k := by
      exact
        MvPowerSeries.truncTotal_subst_eq_truncTotal_truncTotal_subst
          (f := H) (a := fun i : σ ↦ inVariable ebar i) hconstant
    _ = (MvPowerSeries.subst (fun i : σ ↦ inVariable ebar i)
          (H'.truncTotal k).toMvPowerSeries).truncTotal k := by
      rw [htrunc]
    _ = (MvPowerSeries.subst (fun i : σ ↦ inVariable ebar i) H').truncTotal k := by
      exact
        (MvPowerSeries.truncTotal_subst_eq_truncTotal_truncTotal_subst
          (f := H') (a := fun i : σ ↦ inVariable ebar i) hconstant).symm

end Langlands.NYLL.PortInternal.M351
