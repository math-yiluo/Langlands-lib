import Langlands.Global.RankinSelberg.ComplexBruhatLinearization
import Langlands.Group.GL.Transvection

/-! # A smooth family of simple-root stabilizers on each lower complex Bruhat cell -/

noncomputable section

open Set
open scoped Classical ContDiff Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexBruhatStabilizer

open Langlands.GeneralLinear (UpperEntryPair permutation permutation_conjugate_entry transvectionUnit
  upperTriangularSubgroup permutationUnipotentMinus mem_permutationUnipotentMinus_iff)
open Langlands.GeneralLinear.UpperUnipotent (mul_adjacent_entry inv_adjacent_entry)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData)
open ComplexOppositeCompactChart (Coordinates oppositePoint contDiff_oppositePoint_val)
open ComplexBruhatGaussChart (allowedLowerEntry cellCoordinates chartSection conjugate_oppositePoint_mem)
open ComplexBruhatChartDerivative (chartVector chartScalar)
open ComplexBruhatLinearization (complexBruhatLinearization)

local notation "Mat" => fun n => Matrix (Fin n) (Fin n) ℂ
local notation "G" => fun n => Langlands.GeneralLinear n ℂ
local notation "N" => fun n => Langlands.GeneralLinear.upperUnipotent n ℂ

variable {n : ℕ}

/-- The entries along the Bruhat cell in the Gauss chart. -/
abbrev TangentCoordinates (w : Equiv.Perm (Fin n)) := {p : UpperEntryPair n // allowedLowerEntry w p} → ℂ

/-- The complementary entries in the Gauss chart. -/
abbrev NormalCoordinates (w : Equiv.Perm (Fin n)) := {p : UpperEntryPair n // ¬ allowedLowerEntry w p} → ℂ

/-- Split the Gaussian lower entries into those along the cell and those transverse to it. -/
def splitCoordinates (w : Equiv.Perm (Fin n)) :
    Coordinates n ≃L[ℝ] TangentCoordinates w × NormalCoordinates w :=
  ({ toEquiv := Equiv.piEquivPiSubtypeProd (allowedLowerEntry w) (fun _ => ℂ)
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : Coordinates n ≃ₗ[ℝ] TangentCoordinates w × NormalCoordinates w).toContinuousLinearEquiv

theorem mem_cellCoordinates_iff_snd_eq_zero (w : Equiv.Perm (Fin n)) (z : Coordinates n) :
    z ∈ cellCoordinates w ↔ (splitCoordinates w z).2 = 0 := by
  change (∀ p, ¬ allowedLowerEntry w p → z p = 0) ↔ (fun p : {p // ¬ allowedLowerEntry w p} => z p.val) = 0
  constructor
  · exact fun h => funext fun p => h p.val p.2
  · exact fun h p hp => congrFun h ⟨p, hp⟩

/-- Insert zero in the normal entries of a cell coordinate. -/
def cellPoint (w : Equiv.Perm (Fin n)) (x : TangentCoordinates w) : Coordinates n :=
  (splitCoordinates w).symm (x, 0)

theorem cellPoint_mem (w : Equiv.Perm (Fin n)) (x : TangentCoordinates w) : cellPoint w x ∈ cellCoordinates w := by
  rw [mem_cellCoordinates_iff_snd_eq_zero, cellPoint, ContinuousLinearEquiv.apply_symm_apply]

theorem contDiff_cellPoint (w : Equiv.Perm (Fin n)) : ContDiff ℝ ∞ (cellPoint w) :=
  (splitCoordinates w).symm.contDiff.comp (contDiff_id.prodMk contDiff_const)

private def cellUnipotent (w : Equiv.Perm (Fin n)) (x : TangentCoordinates w) : N n :=
  ⟨(permutation n ℂ w)⁻¹ * oppositePoint (cellPoint w x) * permutation n ℂ w,
    ((mem_permutationUnipotentMinus_iff n ℂ w _).mp
      ((conjugate_oppositePoint_mem w (cellPoint w x)).mpr (cellPoint_mem w x))).1⟩

private theorem contDiff_cellUnipotent_val (w : Equiv.Perm (Fin n)) :
    ContDiff ℝ ∞ (fun x : TangentCoordinates w => (cellUnipotent w x).val.val) := by
  exact (contDiff_const.mul ((contDiff_oppositePoint_val n).comp (contDiff_cellPoint w))).mul contDiff_const

private theorem contDiff_cellUnipotent_inv_val (w : Equiv.Perm (Fin n)) :
    ContDiff ℝ ∞ (fun x : TangentCoordinates w => ((cellUnipotent w x).val⁻¹ : G n).val) := by
  simp_rw [← Ring.inverse_unit]
  refine contDiff_iff_contDiffAt.mpr fun x => ?_
  have h : ContDiffAt ℝ ∞ (Ring.inverse : Mat n → Mat n) (cellUnipotent w x).val.val :=
    contDiffAt_ringInverse ℝ (cellUnipotent w x).val
  exact h.comp x (contDiff_cellUnipotent_val w).contDiffAt

private theorem single_strict_upper {i j : Fin n} (hij : i < j) (c : ℂ) (p q : Fin n) (hqp : q ≤ p) :
    Matrix.single i j c p q = 0 := by
  rw [Matrix.single_apply, ite_eq_right]
  rintro ⟨rfl, rfl⟩
  exact (not_le_of_gt hij) hqp

private theorem conjugate_single (w : Equiv.Perm (Fin n)) {i j : Fin n} (hij : i ≠ j) (c : ℂ) :
    (permutation n ℂ w).val * Matrix.single i j c * (permutation n ℂ w)⁻¹.val =
      Matrix.single (w i) (w j) c := by
  let P := permutation n ℂ w
  let t : G n := transvectionUnit i j hij c
  have ht : t.val = 1 + Matrix.single i j c := rfl
  have hConj : (P * t * P⁻¹).val = 1 + P.val * Matrix.single i j c * P⁻¹.val := by
    rw [Units.val_mul, Units.val_mul, ht, mul_add, mul_one, add_mul, Units.mul_inv]
  ext p q
  have h := permutation_conjugate_entry n ℂ w t p q
  change (P * t * P⁻¹).val p q = t.val (w.symm p) (w.symm q) at h
  rw [hConj, ht, Matrix.add_apply, Matrix.add_apply] at h
  have hId : (1 : Mat n) (w.symm p) (w.symm q) = (1 : Mat n) p q := by
    simp only [Matrix.one_apply, Equiv.apply_eq_iff_eq]
  rw [hId] at h
  have hSingle : Matrix.single i j c (w.symm p) (w.symm q) = Matrix.single (w i) (w j) c p q := by
    simp only [Matrix.single_apply, ← Equiv.eq_symm_apply]
  exact (add_left_cancel h).trans hSingle

private theorem conjugate_sq_zero (u : G n) (X : Mat n) (hX : X * X = 0) :
    (u.val * X * u⁻¹.val) * (u.val * X * u⁻¹.val) = 0 := by
  calc
    _ = u.val * X * (u⁻¹.val * u.val) * X * u⁻¹.val := by simp only [mul_assoc]
    _ = _ := by rw [Units.inv_mul, mul_one, mul_assoc u.val X X, hX, mul_zero, zero_mul]

section SimpleRoot

variable {r : ℕ}

private def simpleDirection (a : ℂˣ) (i : Fin r) : Mat (r + 1) :=
  Matrix.single i.castSucc i.succ ((a : ℂ)⁻¹)

private def simpleTransvection (a : ℂˣ) (i : Fin r) : N (r + 1) := by
  let t : G (r + 1) := transvectionUnit i.castSucc i.succ Fin.castSucc_lt_succ.ne ((a : ℂ)⁻¹)
  refine ⟨t, fun p q hpq => ?_, fun p => ?_⟩
  · change q < p at hpq
    change (1 : Mat (r + 1)) p q + simpleDirection a i p q = 0
    rw [Matrix.one_apply_ne hpq.ne', zero_add]
    exact single_strict_upper Fin.castSucc_lt_succ _ p q hpq.le
  · change (1 : Mat (r + 1)) p p + Matrix.single i.castSucc i.succ ((a : ℂ)⁻¹) p p = 1
    rw [Matrix.one_apply_eq, single_strict_upper Fin.castSucc_lt_succ _ p p le_rfl, add_zero]

private theorem simpleTransvection_val (a : ℂˣ) (i : Fin r) :
    (simpleTransvection a i).val.val = 1 + simpleDirection a i := rfl

private theorem simpleDirection_sq (a : ℂˣ) (i : Fin r) : simpleDirection a i * simpleDirection a i = 0 := by
  unfold simpleDirection
  exact Matrix.single_mul_single_of_ne (h := Fin.castSucc_lt_succ.ne') ..

private theorem simpleDirection_sum (a : ℂˣ) (i : Fin r) :
    (∑ j : Fin r, simpleDirection a i j.castSucc j.succ) = (a : ℂ)⁻¹ := by
  rw [Finset.sum_eq_single i]
  · simp [simpleDirection]
  · intro j _ hji
    simp [simpleDirection, Ne.symm hji]
  · simp

private theorem simpleDirection_frequency (a : ℂˣ) (i : Fin r) :
    complexWhittakerFrequency a (simpleDirection a i) = ((4 * Real.pi : ℝ) : ℂ) * Complex.I := by
  rw [complexWhittakerFrequency, simpleDirection_sum, mul_inv_cancel₀ a.ne_zero, Algebra.trace_complex_apply]
  simp only [Complex.one_re]
  push_cast
  ring

private def stabilizingDirection (w : Equiv.Perm (Fin (r + 1))) (a : ℂˣ) (i : Fin r)
    (x : TangentCoordinates w) : Mat (r + 1) :=
  (cellUnipotent w x).val.val * simpleDirection a i * ((cellUnipotent w x).val⁻¹ : G (r + 1)).val

private theorem contDiff_stabilizingDirection (w : Equiv.Perm (Fin (r + 1))) (a : ℂˣ) (i : Fin r) :
    ContDiff ℝ ∞ (stabilizingDirection w a i) :=
  ((contDiff_cellUnipotent_val w).mul contDiff_const).mul (contDiff_cellUnipotent_inv_val w)

set_option maxHeartbeats 850000 in
private theorem stabilizingDirection_properties (w : Equiv.Perm (Fin (r + 1))) (a : ℂˣ) (i : Fin r)
    (x : TangentCoordinates w) :
    (∀ p q, q ≤ p → stabilizingDirection w a i x p q = 0) ∧
    complexWhittakerFrequency a (stabilizingDirection w a i x) = ((4 * Real.pi : ℝ) : ℂ) * Complex.I := by
  let U := cellUnipotent w x
  let T := simpleTransvection a i
  let v := U * T * U⁻¹
  let X := stabilizingDirection w a i x
  have hT : T.val.val = 1 + simpleDirection a i := simpleTransvection_val a i
  have hX : v.val.val = 1 + X := by
    change U.val.val * T.val.val * U.val⁻¹.val = _
    rw [hT, mul_add, add_mul, mul_one, Units.mul_inv]
    rfl
  refine ⟨fun p q hpq => ?_, ?_⟩
  · rcases hpq.lt_or_eq with hpq | rfl
    · have hh := v.2.1 hpq
      change v.val.val p q = 0 at hh
      simpa only [hX, Matrix.add_apply, Matrix.one_apply_ne hpq.ne', zero_add] using hh
    · have hh := v.2.2 q
      change v.val.val q q = 1 at hh
      rw [hX, Matrix.add_apply, Matrix.one_apply_eq, add_eq_left] at hh
      exact hh
  · have hEntry (j : Fin r) : X j.castSucc j.succ = simpleDirection a i j.castSucc j.succ := by
      have h := mul_adjacent_entry (U * T) U⁻¹ j
      rw [mul_adjacent_entry U T j, inv_adjacent_entry U j] at h
      change v.val.val j.castSucc j.succ = U.val.val j.castSucc j.succ + T.val.val j.castSucc j.succ -
        U.val.val j.castSucc j.succ at h
      rw [add_sub_cancel_left] at h
      simpa only [hX, hT, Matrix.add_apply, Matrix.one_apply_ne Fin.castSucc_lt_succ.ne,
        zero_add] using h
    change complexWhittakerFrequency a X = _
    rw [complexWhittakerFrequency]
    simp_rw [hEntry]
    exact simpleDirection_frequency a i

private theorem stabilizingDirection_fixed (w : Equiv.Perm (Fin (r + 1))) (a : ℂˣ) (i : Fin r)
    (x : TangentCoordinates w) :
    (chartSection w (cellPoint w x)).val * stabilizingDirection w a i x =
      ((permutation (r + 1) ℂ w).val * simpleDirection a i * (permutation (r + 1) ℂ w)⁻¹.val) *
        (chartSection w (cellPoint w x)).val := by
  let S := chartSection w (cellPoint w x)
  let U := cellUnipotent w x
  let P := permutation (r + 1) ℂ w
  have hSU : S * U.val = P := by
    change ((oppositePoint (cellPoint w x))⁻¹ * P) *
      (P⁻¹ * oppositePoint (cellPoint w x) * P) = P
    group
  have hUS : U.val⁻¹ = P⁻¹ * S := by rw [← hSU]; group
  change S.val * (U.val.val * simpleDirection a i * U.val⁻¹.val) =
    P.val * simpleDirection a i * P⁻¹.val * S.val
  rw [← mul_assoc, ← mul_assoc S.val U.val.val, ← Units.val_mul, hSU, hUS, Units.val_mul]
  simp only [mul_assoc]

/-- If the permutation is not strictly decreasing, it has a simple adjacent ascent. -/
theorem exists_adjacent_ascent (w : Equiv.Perm (Fin (r + 1))) (hw : ¬ StrictAnti w) :
    ∃ i : Fin r, w i.castSucc < w i.succ := by
  by_contra! h
  apply hw
  apply Fin.strictAnti_iff_succ_lt.mpr
  intro i
  exact lt_of_le_of_ne (h i) (fun he => Fin.castSucc_lt_succ.ne (w.injective he.symm))

/-- The cell directions can be chosen smoothly with a fixed nonzero imaginary Whittaker frequency.
They kill the coordinate and scalar terms on the cell and yield cube-zero fixed-direction derivatives. -/
def ComplexBruhatStabilizerStatement : Prop :=
  ∀ (r : ℕ) (ds : List ComplexCharacterData) (a : ℂˣ) (w : Equiv.Perm (Fin (r + 1))),
    (¬ StrictAnti w) →
    ∃ X : TangentCoordinates w → Mat (r + 1), ContDiff ℝ ∞ X ∧
      ∀ x : TangentCoordinates w,
        (∀ p q, q ≤ p → X x p q = 0) ∧
        complexWhittakerFrequency a (X x) = ((4 * Real.pi : ℝ) : ℂ) * Complex.I ∧
        chartVector w (X x) (cellPoint w x) = 0 ∧ chartScalar w ds (X x) (cellPoint w x) = 0 ∧
        fderiv ℝ (chartVector w (X x)) (cellPoint w x) ^ 3 = 0

theorem complexBruhatStabilizer : ComplexBruhatStabilizerStatement := by
  intro r ds a w hw
  obtain ⟨i, hi⟩ := exists_adjacent_ascent w hw
  let P := permutation (r + 1) ℂ w
  let A := P.val * simpleDirection a i * P⁻¹.val
  have hA : ∀ p q, q ≤ p → A p q = 0 := by
    have he : A = Matrix.single (w i.castSucc) (w i.succ) ((a : ℂ)⁻¹) :=
      conjugate_single w Fin.castSucc_lt_succ.ne _
    rw [he]
    exact single_strict_upper hi _
  have hA2 : A * A = 0 := conjugate_sq_zero P _ (simpleDirection_sq a i)
  refine ⟨stabilizingDirection w a i, contDiff_stabilizingDirection w a i, fun x => ?_⟩
  obtain ⟨hU, hFreq⟩ := stabilizingDirection_properties w a i x
  have hX2 : stabilizingDirection w a i x * stabilizingDirection w a i x = 0 :=
    conjugate_sq_zero (cellUnipotent w x).val _ (simpleDirection_sq a i)
  exact ⟨hU, hFreq, complexBruhatLinearization (r + 1) ds w (cellPoint w x) A
    (stabilizingDirection w a i x) hA hA2 hX2 (stabilizingDirection_fixed w a i x)⟩

end SimpleRoot
end Langlands.Global.RankinSelbergGlobal.ComplexBruhatStabilizer
