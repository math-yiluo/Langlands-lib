import Langlands.Global.RankinSelberg.RealGodementKernelReflection
import Langlands.Group.GL.UpperUnipotentEntryCoordinates

/-! # The unipotent coordinates of the real Godement rectangle -/

noncomputable section

open Langlands.GeneralLinear Langlands.HarmonicAnalysis
open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal
open MeasureTheory

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

variable {m : ℕ}

local instance (d : ℕ) : MeasurableSpace (GeneralLinear.upperUnipotent d ℝ) := borel _
local instance (d : ℕ) : BorelSpace (GeneralLinear.upperUnipotent d ℝ) := ⟨rfl⟩

private def stepUpperIndex (m : ℕ) : StepCoordinates m ≃ UpperEntryPair (m + 1) where
  toFun q := ⟨(q.val.1.succ.rev, q.val.2.rev), Fin.rev_lt_rev.mpr (Nat.lt_succ_of_le q.property)⟩
  invFun q :=
    let h : q.val.1.rev ≠ 0 := Fin.ne_of_gt (lt_of_le_of_lt (Fin.zero_le _)
      (Fin.rev_lt_rev.mpr q.property))
    ⟨(q.val.1.rev.pred h, q.val.2.rev), by
      have hlt := Fin.rev_lt_rev.mpr q.property
      change q.val.2.rev.val < q.val.1.rev.val at hlt
      simp only [Fin.val_pred]
      omega⟩
  left_inv q := by
    apply Subtype.ext
    apply Prod.ext
    · simp
    · simp
  right_inv q := by
    apply Subtype.ext
    apply Prod.ext
    · simp
    · simp

/-- Put the free entries of the Godement chart into the actual upper-unipotent
coordinates by the long Weyl reversal of both matrix indices. -/
def upperStepChart (m : ℕ) : (StepCoordinates m → ℝ) ≃ₜ GeneralLinear.upperUnipotent (m + 1) ℝ :=
  (Homeomorph.piCongrLeft (Y := fun _ => ℝ) (stepUpperIndex m)).trans
    (upperEntryCoordinates (m + 1)).symm

private theorem upperStepChart_free (z : StepCoordinates m → ℝ) (q : StepCoordinates m) :
    (upperStepChart m z).val q.val.1.succ.rev q.val.2.rev = z q := by
  let p := stepUpperIndex m q
  change ((upperEntryCoordinates (m + 1) (K := ℝ)).symm
    (Homeomorph.piCongrLeft (Y := fun _ => ℝ) (stepUpperIndex m) z)).val.val p.val.1 p.val.2 = z q
  rw [upperEntryCoordinates_symm_upper _ p.property]
  exact Homeomorph.piCongrLeft_apply_apply (Y := fun _ => ℝ) (stepUpperIndex m) z q

/-- The Godement rectangle consists of the trailing rows of the lower matrix
obtained by conjugating the upper step chart by the long Weyl element. -/
theorem stepRectangle_eq_upperStepChart (z : StepCoordinates m → ℝ) (i : Fin m) (j : Fin (m + 1)) :
    stepRectangle z i j = (upperStepChart m z).val i.succ.rev j.rev := by
  by_cases h : j.val ≤ i.val
  · rw [stepRectangle, dite_eq_left h]
    exact (upperStepChart_free z ⟨(i, j), h⟩).symm
  · rw [stepRectangle, dite_eq_right h]
    by_cases he : j.val = i.val + 1
    · have hij : j = i.succ := Fin.ext he
      subst j
      rw [ite_eq_left he, UpperUnipotent.entry_diag]
    · have hij : i.succ < j := by
        change i.val + 1 < j.val
        omega
      rw [ite_eq_right he, UpperUnipotent.entry_eq_zero _ (Fin.rev_lt_rev.mpr hij)]

private def stepBoundary (m : ℕ) : Fin m ≃ {q : StepCoordinates m // q.val.2.val = q.val.1.val} where
  toFun i := ⟨⟨(i, i.castSucc), le_rfl⟩, rfl⟩
  invFun q := q.val.val.1
  left_inv _ := rfl
  right_inv q := Subtype.ext (Subtype.ext (Prod.ext rfl (Fin.ext q.property.symm)))

/-- The phase is the usual first-superdiagonal sum in the actual upper chart. -/
theorem stepPhase_eq_upperStepChart (z : StepCoordinates m → ℝ) :
    stepPhase z = ∑ i : Fin m, (upperStepChart m z).val i.castSucc i.succ := by
  calc
    _ = ∑ q : StepCoordinates m, if q.val.2.val = q.val.1.val then z q else 0 := by
      change (∑ q : StepCoordinates m, z q * (if q.val.2.val = q.val.1.val then 1 else 0)) = _
      simp only [mul_ite, mul_one, mul_zero]
    _ = ∑ q : {q : StepCoordinates m // q.val.2.val = q.val.1.val}, z q := by
      rw [← Finset.sum_filter]
      symm
      simpa only [Finset.subtype_univ] using
        (Finset.sum_subtype_eq_sum_filter (s := Finset.univ) z
          (p := fun q => q.val.2.val = q.val.1.val))
    _ = ∑ i : Fin m, z ((stepBoundary m i).val) :=
      (Equiv.sum_comp (stepBoundary m) (fun q => z q.val)).symm
    _ = ∑ i : Fin m, (upperStepChart m z).val i.rev.castSucc i.rev.succ := by
      apply Finset.sum_congr rfl
      intro i _
      change z ⟨(i, i.castSucc), le_rfl⟩ = _
      have h := (upperStepChart_free z ⟨(i, i.castSucc), le_rfl⟩).symm
      change z ⟨(i, i.castSucc), le_rfl⟩ = (upperStepChart m z).val i.succ.rev i.castSucc.rev at h
      simpa only [Fin.rev_succ, Fin.rev_castSucc] using h
    _ = _ := Equiv.sum_comp Fin.revPerm (fun i : Fin m => (upperStepChart m z).val i.castSucc i.succ)

/-- The specified self-dual scalar entry product on the upper unipotent group. -/
def upperStepHaar (m : ℕ) (a : ℝˣ) : Measure (GeneralLinear.upperUnipotent (m + 1) ℝ) :=
  (upperEntryProductMeasure (realSelfDualMeasure a) (m + 1)).map (upperEntryCoordinates (m + 1)).symm

theorem upperStepHaar_isHaar (m : ℕ) (a : ℝˣ) : (upperStepHaar m a).IsHaarMeasure :=
  upperEntryProductMeasure_isHaar (realSelfDualMeasure a)

theorem measurePreserving_upperStepChart (m : ℕ) (a : ℝˣ) :
    MeasurePreserving (upperStepChart m) (stepMeasure m a) (upperStepHaar m a) := by
  have hπ := measurePreserving_piCongrLeft
    (fun _ : UpperEntryPair (m + 1) => (realSelfDualMeasure a).measure) (stepUpperIndex m)
  have he : MeasurePreserving ((upperEntryCoordinates (m + 1) (K := ℝ)).symm)
      (upperEntryProductMeasure (realSelfDualMeasure a) (m + 1)) (upperStepHaar m a) :=
    ⟨(upperEntryCoordinates (m + 1) (K := ℝ)).symm.continuous.measurable, rfl⟩
  exact he.comp hπ

/-- The actual unipotent chart for the Godement rectangle, including its phase
and the exact entry-product Haar measure. -/
def RealGodementStepChartStatement : Prop :=
  ∀ (m : ℕ) (a : ℝˣ), MeasurePreserving (upperStepChart m) (stepMeasure m a) (upperStepHaar m a) ∧
    (upperStepHaar m a).IsHaarMeasure ∧
    ∀ (z : StepCoordinates m → ℝ),
      (∀ (i : Fin m) (j : Fin (m + 1)), stepRectangle z i j =
        (upperStepChart m z).val i.succ.rev j.rev) ∧
      stepPhase z = ∑ i : Fin m, (upperStepChart m z).val i.castSucc i.succ

theorem realGodementStepChart : RealGodementStepChartStatement := by
  intro m a
  exact ⟨measurePreserving_upperStepChart m a, upperStepHaar_isHaar m a,
    fun z => ⟨stepRectangle_eq_upperStepChart z, stepPhase_eq_upperStepChart z⟩⟩

end Langlands.Global.RankinSelbergGlobal.RealGodement
