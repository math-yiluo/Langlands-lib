/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 488, 2026-11-14: isolate the source theorem M351.004
from Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean,
upstream commit fbd320cd8b1b06487c58227e92eb135794267709, as a proof of
the published target in the Langlands.NYLL namespace.
Modified by Worker 517, 2026-11-16: import only the published target module;
inline the needed directions of M351.001 and the source-private proofs
M351.002–003 as local facts; compute the constant coefficient of inVariable
directly using Mathlib instead of the separate M348.002 theorem.
The original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.U002.Statements

/-!
# Finite-degree continuity of intertwining defects

Proof of M351.004: agreement of two zero-constant series through total
degree `m` implies agreement of their intertwining defects through that
degree. The truncation and substitution arguments are local to this proof.
-/

attribute [local instance] Classical.propDecidable

universe u v w

namespace Langlands.NYLL.LubinTate
namespace SameUniformizer

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}
variable {σ : Type w}

/-- The coefficients through total degree `m` of an intertwining defect
depend only on the coefficients of its proposed intertwiner through `m`. -/
theorem coeff_defect_eq_of_coeff_eq_degree_le [Finite σ]
    (e ebar : LubinTateSeries F π)
    {H H' : MvPowerSeries σ F.valuationSubring}
    (hH : MvPowerSeries.constantCoeff H = 0)
    (hH' : MvPowerSeries.constantCoeff H' = 0)
    {m : ℕ}
    (hcoeff : ∀ q : σ →₀ ℕ, q.degree ≤ m →
      MvPowerSeries.coeff q H = MvPowerSeries.coeff q H')
    {d : σ →₀ ℕ} (hd : d.degree ≤ m) :
    coeff_defect_eq_of_coeff_eq_degree_leStatement e ebar hH hH' hcoeff hd := by
  let k := m + 1
  have htrunc : H.truncTotal k = H'.truncTotal k := by
    apply MvPolynomial.ext
    intro q
    by_cases hq : q.degree < k
    · rw [MvPowerSeries.coeff_truncTotal H hq,
        MvPowerSeries.coeff_truncTotal H' hq]
      exact hcoeff q (Nat.lt_succ_iff.mp hq)
    · rw [MvPowerSeries.coeff_truncTotal_eq_zero H (not_lt.mp hq),
        MvPowerSeries.coeff_truncTotal_eq_zero H' (not_lt.mp hq)]
  have hleft :
      (PowerSeries.subst H e.toPowerSeries).truncTotal k =
        (PowerSeries.subst H' e.toPowerSeries).truncTotal k := by
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
            e.toPowerSeries).truncTotal k :=
        MvPowerSeries.truncTotal_subst_eq_truncTotal_subst_truncTotal_of_le
          (f := e.toPowerSeries) (a := fun _ : Unit ↦ H)
          (x := fun _ : Unit ↦ k) hHsubst.const (fun _ ↦ le_rfl)
      _ = (MvPowerSeries.subst
            (fun _ : Unit ↦ (H'.truncTotal k).toMvPowerSeries)
            e.toPowerSeries).truncTotal k := by rw [htrunc]
      _ = (MvPowerSeries.subst (fun _ : Unit ↦ H')
            e.toPowerSeries).truncTotal k :=
        (MvPowerSeries.truncTotal_subst_eq_truncTotal_subst_truncTotal_of_le
          (f := e.toPowerSeries) (a := fun _ : Unit ↦ H')
          (x := fun _ : Unit ↦ k) hH'subst.const (fun _ ↦ le_rfl)).symm
  have hright :
      (MvPowerSeries.subst (fun i : σ ↦ inVariable ebar i) H).truncTotal k =
        (MvPowerSeries.subst
          (fun i : σ ↦ inVariable ebar i) H').truncTotal k := by
    have hconstant :
        ∀ i : σ, MvPowerSeries.constantCoeff (inVariable ebar i) = 0 := by
      intro i
      exact PowerSeries.constantCoeff_subst_eq_zero
        (by simp) ebar.toPowerSeries ebar.constantCoeff_eq_zero
    calc
      (MvPowerSeries.subst (fun i : σ ↦ inVariable ebar i) H).truncTotal k =
          (MvPowerSeries.subst (fun i : σ ↦ inVariable ebar i)
            (H.truncTotal k).toMvPowerSeries).truncTotal k :=
        MvPowerSeries.truncTotal_subst_eq_truncTotal_truncTotal_subst
          (f := H) (a := fun i : σ ↦ inVariable ebar i) hconstant
      _ = (MvPowerSeries.subst (fun i : σ ↦ inVariable ebar i)
            (H'.truncTotal k).toMvPowerSeries).truncTotal k := by rw [htrunc]
      _ = (MvPowerSeries.subst (fun i : σ ↦ inVariable ebar i) H').truncTotal k :=
        (MvPowerSeries.truncTotal_subst_eq_truncTotal_truncTotal_subst
          (f := H') (a := fun i : σ ↦ inVariable ebar i) hconstant).symm
  have hdefect :
      (defect e ebar H).truncTotal k =
        (defect e ebar H').truncTotal k := by
    calc
      (defect e ebar H).truncTotal k =
          (PowerSeries.subst H e.toPowerSeries).truncTotal k -
            (MvPowerSeries.subst
              (fun i : σ ↦ inVariable ebar i) H).truncTotal k := by
        rw [defect, map_sub]
      _ = (PowerSeries.subst H' e.toPowerSeries).truncTotal k -
            (MvPowerSeries.subst
              (fun i : σ ↦ inVariable ebar i) H').truncTotal k := by
        rw [hleft, hright]
      _ = (defect e ebar H').truncTotal k := by
        rw [defect, map_sub]
  have hd' : d.degree < k := Nat.lt_succ_iff.mpr hd
  calc
    MvPowerSeries.coeff d (defect e ebar H) =
        ((defect e ebar H).truncTotal k).coeff d :=
      (MvPowerSeries.coeff_truncTotal (defect e ebar H) hd').symm
    _ = ((defect e ebar H').truncTotal k).coeff d := by rw [hdefect]
    _ = MvPowerSeries.coeff d (defect e ebar H') :=
      MvPowerSeries.coeff_truncTotal (defect e ebar H') hd'

end SameUniformizer
end Langlands.NYLL.LubinTate
