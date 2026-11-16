/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 628, 2026-11-16: isolate the proof of the source private
theorem M351.019 from commit fbd320cd8b1b06487c58227e92eb135794267709,
using the published Langlands.NYLL definitions and proposition targets.
Import the published prerequisite proofs M351.017 and M351.018, replace
the source-private linear model by d011, and state the theorem against the
published d019Statement. The original LICENSE and NOTICE remain in
licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.MonomialSubst.InVariableStatements
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.MonomialSubst.D017Proof
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.MonomialSubst.D018Proof

/-!
# Low-degree coefficients of a substituted monomial

Proof of NYLL M351.019 using the order comparison with the linear model and
the coefficient formula for that model.
-/

noncomputable section

attribute [local instance] Classical.propDecidable

universe u v w

namespace Langlands.NYLL.PortInternal.M351

open Langlands.NYLL.LocalFieldTheory.DiscreteValuationField
open Langlands.NYLL.LubinTate Langlands.NYLL.LubinTate.SameUniformizer

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}
variable {σ : Type w}

/-- The coefficient of a substituted monomial in total degree at most its
original degree is its linear-model coefficient (NYLL M351.019). -/
theorem d019 [Finite σ]
    (ebar : LubinTateSeries F π)
    (q d : σ →₀ ℕ) (hq : q.degree ≤ d.degree)
    (c : F.valuationSubring) :
    d019Statement ebar q d hq c := by
  unfold d019Statement
  have horder := d017 ebar d c
  have hlt :
      (q.degree : ℕ∞) <
        (MvPowerSeries.subst (fun i : σ => inVariable ebar i)
            (MvPowerSeries.monomial d c) -
          MvPowerSeries.subst
            (d011 (σ := σ) π)
            (MvPowerSeries.monomial d c)).order := by
    have hqNat : q.degree < d.degree + 1 :=
      Nat.lt_succ_of_le hq
    have hqCast :
        (q.degree : ℕ∞) < ((d.degree + 1 : ℕ) : ℕ∞) := by
      exact_mod_cast hqNat
    exact hqCast.trans_le horder
  have hcoeff := MvPowerSeries.coeff_of_lt_order hlt
  rw [map_sub, sub_eq_zero] at hcoeff
  rw [hcoeff, d018]

end Langlands.NYLL.PortInternal.M351

end
