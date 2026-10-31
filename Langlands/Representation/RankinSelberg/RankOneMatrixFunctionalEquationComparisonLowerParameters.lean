import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonAffineParameters
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonTriangularFourier
import Langlands.Group.GL.UpperUnipotentEntryCoordinates

/-! Product parameters for the shifted lower affine slice. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory MeasureTheory.Measure
open scoped BigOperators

namespace Langlands.HarmonicAnalysis

open GeneralLinear

universe uK

/-- The column after the first index of a strict-upper position. -/
def shiftedUpperEntryColumn {n : ℕ} (p : UpperEntryPair (n + 1)) : Fin (n + 1) :=
  ⟨p.1.1.val + 1, by
    have h : p.1.1.val < p.1.2.val := p.2
    have hlt : p.1.2.val < n + 1 := p.1.2.isLt
    omega⟩

private def lowerEntryIndex (n : ℕ) : Option (UpperEntryPair (n + 1)) →
    RectangularFreeEntry (shiftedLowerSliceColumns n)
  | none => ⟨Fin.last n, ⟨0, by simp [shiftedLowerSliceColumns]⟩⟩
  | some p => ⟨p.1.2, ⟨shiftedUpperEntryColumn p, by
      simp only [shiftedLowerSliceColumns, Finset.mem_filter, Finset.mem_univ, true_and]
      apply Or.inr
      constructor
      · change 0 < p.1.1.val + 1
        omega
      · change p.1.1.val + 1 ≤ p.1.2.val
        have := p.2
        omega⟩⟩

private theorem lowerEntryIndex_injective (n : ℕ) : Function.Injective (lowerEntryIndex n) := by
  intro x y h
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some p =>
      have hc := congrArg (fun q : RectangularFreeEntry (shiftedLowerSliceColumns n) =>
        q.2.1.val) h
      change 0 = p.1.1.val + 1 at hc
      omega
  | some p =>
    cases y with
    | none =>
      have hc := congrArg (fun q : RectangularFreeEntry (shiftedLowerSliceColumns n) =>
        q.2.1.val) h
      change p.1.1.val + 1 = 0 at hc
      omega
    | some q =>
      have hr := congrArg (fun q : RectangularFreeEntry (shiftedLowerSliceColumns n) =>
        q.1.val) h
      have hc := congrArg (fun q : RectangularFreeEntry (shiftedLowerSliceColumns n) =>
        q.2.1.val) h
      apply congrArg some
      apply Subtype.ext
      apply Prod.ext
      · apply Fin.ext
        change p.1.1.val + 1 = q.1.1.val + 1 at hc
        omega
      · exact Fin.ext hr

private theorem lowerEntryIndex_surjective (n : ℕ) : Function.Surjective (lowerEntryIndex n) := by
  intro q
  obtain ⟨i, j, hj⟩ := q
  have hsel : (j = 0 ∧ i = Fin.last n) ∨ (0 < j ∧ j ≤ i) := by
    simpa only [shiftedLowerSliceColumns, Finset.mem_filter, Finset.mem_univ, true_and] using hj
  by_cases hz : j = 0
  · have hi : i = Fin.last n := by
      rcases hsel with h | h
      · exact h.2
      · exact (by simpa [hz] using h.1 : False).elim
    subst i
    subst j
    exact ⟨none, rfl⟩
  · have hp : 0 < j := Fin.pos_of_ne_zero hz
    have hji : j ≤ i := by
      rcases hsel with h | h
      · exact (hz h.1).elim
      · exact h.2
    let k : Fin (n + 1) := ⟨j.val - 1, by have := j.isLt; omega⟩
    have hki : k < i := by
      change j.val - 1 < i.val
      change 0 < j.val at hp
      change j.val ≤ i.val at hji
      omega
    refine ⟨some ⟨(k, i), hki⟩, ?_⟩
    change (⟨i, ⟨shiftedUpperEntryColumn ⟨(k, i), hki⟩, _⟩⟩ :
      RectangularFreeEntry (shiftedLowerSliceColumns n)) = ⟨i, ⟨j, hj⟩⟩
    apply Sigma.ext (show i = i from rfl)
    apply heq_of_eq
    apply Subtype.ext
    apply Fin.ext
    change j.val - 1 + 1 = j.val
    change 0 < j.val at hp
    omega

/-- The selected lower entries are exactly the final first-column entry and
one shifted position for each strict upper entry. -/
def shiftedLowerEntryEquiv (n : ℕ) : Option (UpperEntryPair (n + 1)) ≃
    RectangularFreeEntry (shiftedLowerSliceColumns n) :=
  Equiv.ofBijective (lowerEntryIndex n)
    ⟨lowerEntryIndex_injective n, lowerEntryIndex_surjective n⟩

variable {K : Type uK} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]
  [LocallyCompactSpace K] [T2Space K]

/-- Fill the shifted lower affine slice using strict-upper scalar coordinates
and one scalar. Strict-upper entries enter with a minus sign. -/
def shiftedLowerParam (n : ℕ) (z : (UpperEntryPair (n + 1) → K) × K) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
  rectangularSliceParam (shiftedLowerSliceColumns n) (negativeSuperdiagonal n)
    ((MeasurableEquiv.piCongrLeft (fun _ => K) (shiftedLowerEntryEquiv n))
      ((MeasurableEquiv.piOptionEquivProd (fun _ : Option (UpperEntryPair (n + 1)) => K)).symm
        (-z.1, z.2)))

/-- The lower parameter map preserves exactly the supplied entry product times
the supplied scalar Haar measure. -/
theorem shiftedLowerParam_preserving (ν : AdditiveHaarMeasure K)
    [SigmaFinite ν.measure] (n : ℕ) :
    MeasurePreserving (shiftedLowerParam n)
      ((upperEntryProductMeasure ν (n + 1)).prod ν.measure)
      (shiftedLowerSliceMeasure ν n) := by
  have hnscalar : MeasurePreserving (fun x : K => -x) ν.measure ν.measure :=
    measurePreserving_neg ν.measure
  have hncoord : MeasurePreserving (fun X : UpperEntryPair (n + 1) → K => -X)
      (upperEntryProductMeasure ν (n + 1)) (upperEntryProductMeasure ν (n + 1)) :=
    measurePreserving_pi (fun _ => ν.measure) (fun _ => ν.measure) (fun _ => hnscalar)
  have hneg : MeasurePreserving (fun z : (UpperEntryPair (n + 1) → K) × K => (-z.1, z.2))
      ((upperEntryProductMeasure ν (n + 1)).prod ν.measure)
      ((upperEntryProductMeasure ν (n + 1)).prod ν.measure) :=
    hncoord.prod (MeasurePreserving.id ν.measure)
  have hopt : MeasurePreserving
      (MeasurableEquiv.piOptionEquivProd (fun _ : Option (UpperEntryPair (n + 1)) => K)).symm
      ((upperEntryProductMeasure ν (n + 1)).prod ν.measure)
      (Measure.pi (fun _ : Option (UpperEntryPair (n + 1)) => ν.measure)) :=
    ⟨(MeasurableEquiv.piOptionEquivProd _).symm.measurable,
      pi_map_piOptionEquivProd (fun _ => ν.measure)⟩
  have hindex := measurePreserving_piCongrLeft
    (α := fun _ : RectangularFreeEntry (shiftedLowerSliceColumns n) => K)
    (fun _ => ν.measure) (shiftedLowerEntryEquiv n)
  exact (rectangularSliceParam_preserving ν (shiftedLowerSliceColumns n)
    (negativeSuperdiagonal n)).comp (hindex.comp (hopt.comp hneg))

omit [TopologicalSpace K] [IsTopologicalRing K] [BorelSpace K]
  [SecondCountableTopology K] [LocallyCompactSpace K] [T2Space K] in
private theorem lowerParam_selected (n : ℕ)
    (z : (UpperEntryPair (n + 1) → K) × K) (o : Option (UpperEntryPair (n + 1))) :
    shiftedLowerParam n z (lowerEntryIndex n o).1 (lowerEntryIndex n o).2.1 =
      o.elim z.2 (fun p => -z.1 p) := by
  change (if h : (lowerEntryIndex n o).2.1 ∈ shiftedLowerSliceColumns n (lowerEntryIndex n o).1 then
    ((MeasurableEquiv.piCongrLeft (fun _ => K) (shiftedLowerEntryEquiv n))
      ((MeasurableEquiv.piOptionEquivProd (fun _ : Option (UpperEntryPair (n + 1)) => K)).symm
        (-z.1, z.2))) ⟨(lowerEntryIndex n o).1, ⟨(lowerEntryIndex n o).2.1, h⟩⟩
    else negativeSuperdiagonal n (lowerEntryIndex n o).1 (lowerEntryIndex n o).2.1) = _
  rw [dite_eq_left (lowerEntryIndex n o).2.2]
  have hi : (⟨(lowerEntryIndex n o).1,
      ⟨(lowerEntryIndex n o).2.1, (lowerEntryIndex n o).2.2⟩⟩ :
      RectangularFreeEntry (shiftedLowerSliceColumns n)) = shiftedLowerEntryEquiv n o := rfl
  rw [hi]
  simp only [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  cases o <;> rfl

omit [TopologicalSpace K] [IsTopologicalRing K] [BorelSpace K]
  [SecondCountableTopology K] [LocallyCompactSpace K] [T2Space K] in
@[simp] theorem shiftedLowerParam_last_zero (n : ℕ)
    (z : (UpperEntryPair (n + 1) → K) × K) :
    shiftedLowerParam n z (Fin.last n) 0 = z.2 :=
  lowerParam_selected n z none

omit [TopologicalSpace K] [IsTopologicalRing K] [BorelSpace K]
  [SecondCountableTopology K] [LocallyCompactSpace K] [T2Space K] in
@[simp] theorem shiftedLowerParam_upperEntry (n : ℕ)
    (z : (UpperEntryPair (n + 1) → K) × K) (p : UpperEntryPair (n + 1)) :
    shiftedLowerParam n z p.1.2 (shiftedUpperEntryColumn p) = -z.1 p :=
  lowerParam_selected n z (some p)

/-- The shift matrix with negative superdiagonal and final first-column entry a. -/
def cyclicShiftMatrix (n : ℕ) (a : K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
  negativeSuperdiagonal n + Matrix.single (Fin.last n) 0 a

omit [TopologicalSpace K] [IsTopologicalRing K] [MeasurableSpace K] [BorelSpace K]
  [SecondCountableTopology K] [LocallyCompactSpace K] [T2Space K] in
private theorem transpose_mul_cyclicShift_zero {n : ℕ}
    (u : upperUnipotent (n + 1) K) (a : K) (i : Fin (n + 1)) :
    (u.val.val.transpose * cyclicShiftMatrix n a) i 0 =
      if i = Fin.last n then a else 0 := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.last n)]
  · simp only [cyclicShiftMatrix, Matrix.add_apply, negativeSuperdiagonal,
      Fin.val_last, Fin.val_zero, Nat.add_one_ne_zero, ite_false,
      Matrix.single_apply, and_self, ite_true, zero_add, Matrix.transpose_apply]
    by_cases hi : i = Fin.last n
    · subst i
      rw [UpperUnipotent.entry_diag]
      simp
    · have hil : i < Fin.last n := lt_of_le_of_ne (Fin.le_last i) hi
      rw [UpperUnipotent.entry_eq_zero u hil]
      simp [hi]
  · intro j _ hj
    simp [cyclicShiftMatrix, negativeSuperdiagonal, Ne.symm hj]
  · simp

omit [TopologicalSpace K] [IsTopologicalRing K] [MeasurableSpace K] [BorelSpace K]
  [SecondCountableTopology K] [LocallyCompactSpace K] [T2Space K] in
private theorem transpose_mul_cyclicShift_succ {n : ℕ}
    (u : upperUnipotent (n + 1) K) (a : K) (i : Fin (n + 1)) (k : Fin n) :
    (u.val.val.transpose * cyclicShiftMatrix n a) i k.succ = -u.val.val k.castSucc i := by
  have hz : (0 : Fin (n + 1)) ≠ k.succ := (Fin.succ_ne_zero k).symm
  rw [Matrix.mul_apply, Finset.sum_eq_single k.castSucc]
  · simp [cyclicShiftMatrix, negativeSuperdiagonal, hz]
  · intro j _ hj
    have hne : j.val ≠ k.val := fun he => hj (Fin.ext he)
    simp [cyclicShiftMatrix, negativeSuperdiagonal, hz, hne]
  · simp

omit [BorelSpace K] [SecondCountableTopology K] [LocallyCompactSpace K] [T2Space K] in
/-- The parameter map is the actual matrix product u-transpose times the shift
matrix. Thus its strict-upper coordinates come from the actual group element. -/
theorem shiftedLowerParam_eq_transpose_mul (n : ℕ)
    (u : upperUnipotent (n + 1) K) (a : K) :
    shiftedLowerParam n (upperEntryCoordinates (n + 1) u, a) =
      u.val.val.transpose * cyclicShiftMatrix n a := by
  ext i j
  refine Fin.cases ?_ (fun k => ?_) j
  · rw [transpose_mul_cyclicShift_zero]
    by_cases hi : i = Fin.last n
    · subst i
      simp only [shiftedLowerParam_last_zero, ite_true]
    · have hm : (0 : Fin (n + 1)) ∉ shiftedLowerSliceColumns n i := by
        simp [shiftedLowerSliceColumns, hi]
      change (if h : (0 : Fin (n + 1)) ∈ shiftedLowerSliceColumns n i then _
        else negativeSuperdiagonal n i 0) = _
      rw [dite_eq_right hm]
      simp [negativeSuperdiagonal, hi]
  · rw [transpose_mul_cyclicShift_succ]
    by_cases hki : k.succ ≤ i
    · have hlt : k.castSucc < i := by
        change k.val < i.val
        change k.val + 1 ≤ i.val at hki
        omega
      let p : UpperEntryPair (n + 1) := ⟨(k.castSucc, i), hlt⟩
      have hc : shiftedUpperEntryColumn p = k.succ := Fin.ext rfl
      rw [← hc]
      exact (shiftedLowerParam_upperEntry n _ p).trans
        (congrArg Neg.neg (upperEntryCoordinates_apply u p))
    · have hm : k.succ ∉ shiftedLowerSliceColumns n i := by
        simp only [shiftedLowerSliceColumns, Finset.mem_filter, Finset.mem_univ, true_and]
        rintro (⟨hz, _⟩ | ⟨_, hle⟩)
        · exact Fin.succ_ne_zero k hz
        · exact hki hle
      change (if h : k.succ ∈ shiftedLowerSliceColumns n i then _
        else negativeSuperdiagonal n i k.succ) = _
      rw [dite_eq_right hm]
      by_cases hi : i = k.castSucc
      · subst i
        simp [negativeSuperdiagonal, UpperUnipotent.entry_diag]
      · have hik : i < k.castSucc := by
          change i.val < k.val
          change ¬k.val + 1 ≤ i.val at hki
          have hine : i.val ≠ k.val := fun he => hi (Fin.ext he)
          omega
        have hne : i.val ≠ k.val := fun he => hi (Fin.ext he)
        rw [UpperUnipotent.entry_eq_zero u hik]
        simp [negativeSuperdiagonal, hne]

/-- Actual transpose-unipotent multiplication realizes the lower slice with
exactly the scalar coordinate product and the supplied scalar Haar measure. -/
theorem shiftedLower_transpose_product_preserving (ν : AdditiveHaarMeasure K)
    [SigmaFinite ν.measure] (n : ℕ) :
    MeasurePreserving
      (fun z : (UpperEntryPair (n + 1) → K) × K =>
        (((upperEntryCoordinates (n + 1)).symm z.1).val.val).transpose *
          cyclicShiftMatrix n z.2)
      ((upperEntryProductMeasure ν (n + 1)).prod ν.measure)
      (shiftedLowerSliceMeasure ν n) := by
  have he : shiftedLowerParam (K := K) n =
      (fun z : (UpperEntryPair (n + 1) → K) × K =>
        (((upperEntryCoordinates (n + 1)).symm z.1).val.val).transpose *
          cyclicShiftMatrix n z.2) := by
    funext z
    simpa only [Homeomorph.apply_symm_apply] using
      shiftedLowerParam_eq_transpose_mul n ((upperEntryCoordinates (n + 1)).symm z.1) z.2
  exact he ▸ shiftedLowerParam_preserving ν n

end Langlands.HarmonicAnalysis
