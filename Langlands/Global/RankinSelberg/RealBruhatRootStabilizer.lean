import Langlands.Global.RankinSelberg.RealWhittakerGauge
import Langlands.Group.GL.UpperBruhatCoordinatesProof
import Langlands.Group.GL.UpperTriangularMaximalSolvable
import Langlands.Representation.Archimedean.RealJacquetFrobeniusProof
import Mathlib.LinearAlgebra.Trace

/-! # A character-detecting simple-root stabilizer on the lower real Bruhat cells -/

noncomputable section

open Langlands.GeneralLinear Langlands.Archimedean Langlands.LocalFactor.Archimedean
open scoped Matrix.Norms.Operator Real

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealBruhatRootStabilizer

open RealWhittakerGauge UpperBruhatCoordinates UpperTriangularMaximalSolvable UpperUnipotent

variable {r : ℕ}
local notation "G" => Langlands.GeneralLinear (r + 1) ℝ
local notation "M" => Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ
local notation "U" => upperUnipotent (r + 1) ℝ
local notation "B" => upperTriangularSubgroup (r + 1) ℝ
local notation "P" => permutation (r + 1) ℝ

/-- Every permutation except the order reversal has an adjacent ascent. -/
theorem exists_adjacent_ascent (w : Equiv.Perm (Fin (r + 1))) (hw : w ≠ Fin.revPerm) :
    ∃ i : Fin r, w i.castSucc < w i.succ := by
  by_contra! h
  have ha : StrictAnti w := Fin.strictAnti_iff_succ_lt.mpr fun i =>
    (h i).lt_of_ne (w.injective.ne i.castSucc_lt_succ.ne')
  have hm : StrictMono (fun j : Fin (r + 1) => (w j).rev) :=
    fun _ _ hij => Fin.rev_lt_rev.mpr (ha hij)
  apply hw
  apply Equiv.ext
  intro j
  have he : (w j).rev = j := hm.apply_eq
  simpa only [Fin.rev_rev, Fin.revPerm_apply] using congrArg Fin.rev he

/-- The root group in the adjacent positions of `i`. -/
def rootUnit (i : Fin r) (t : ℝ) : G := matrixExpUnit (r + 1) (t • rootMatrix i)

private theorem rootUnit_eq_transvection (i : Fin r) (t : ℝ) :
    rootUnit i t = transvectionUnit i.castSucc i.succ i.castSucc_lt_succ.ne t := by
  apply Units.ext
  rw [rootUnit, matrixExpUnit_rootMatrix_val]
  ext p q
  simp only [Matrix.add_apply, Matrix.smul_apply, rootMatrix_apply, transvectionUnit,
    Matrix.transvection, Matrix.single_apply, smul_eq_mul]
  split_ifs <;> simp

private theorem rootUnit_neg_mul (i : Fin r) (t : ℝ) : rootUnit i (-t) * rootUnit i t = 1 := by
  rw [rootUnit, rootUnit, ← matrixExpUnit_add_smul, neg_add_cancel, zero_smul, matrixExpUnit_zero]

/-- The left member of the stabilizer of `b * p * v`. -/
def leftUnit (b : B) (w : Equiv.Perm (Fin (r + 1))) (i : Fin r) (t : ℝ) : G :=
  (b.val * P w) * rootUnit i (-t) * (b.val * P w)⁻¹

/-- The right member of the stabilizer of `b * p * v`. -/
def rightUnit (v : U) (i : Fin r) (t : ℝ) : U :=
  v⁻¹ * ⟨rootUnit i t, matrixExpUnit_rootMatrix_mem i t⟩ * v

/-- The left root stays upper when the permutation has an ascent at `i`. -/
theorem leftUnit_mem_upper (b : B) (w : Equiv.Perm (Fin (r + 1))) (i : Fin r)
    (hi : w i.castSucc < w i.succ) (t : ℝ) : leftUnit b w i t ∈ U := by
  have h : leftUnit b w i t = b.val *
      (P w * rootUnit i (-t) * (P w)⁻¹) * b.val⁻¹ := by unfold leftUnit; group
  rw [h, rootUnit_eq_transvection, permutation_conjugate_transvection]
  let u := transvectionUnit (w i.castSucc) (w i.succ) hi.ne (-t)
  have hu : u ∈ U := by
    refine ⟨transvection_mem_upper hi _, fun j => ?_⟩
    change (Matrix.transvection (w i.castSucc) (w i.succ) (-t)) j j = 1
    have he : ¬ (w i.castSucc = j ∧ w i.succ = j) := fun h => hi.ne (h.1.trans h.2.symm)
    simp [Matrix.transvection, he]
  have huB : b.val * u ∈ B := mul_mem b.property hu.1
  have hbInv : b.val⁻¹ ∈ B := inv_mem b.property
  have hb : b.val * u * b.val⁻¹ ∈ B := mul_mem huB hbInv
  refine ⟨hb, fun j => ?_⟩
  have h₁ := RealJacquetFrobenius.upper_mul_apply_self b.property hu.1 j
  have h₂ := RealJacquetFrobenius.upper_mul_apply_self huB hbInv j
  change (b.val.val * u.val * b.val⁻¹.val) j j =
    (b.val.val * u.val) j j * b.val⁻¹.val j j at h₂
  have hud : u.val j j = 1 := hu.2 j
  change (b.val.val * u.val * b.val⁻¹.val) j j = 1
  rw [h₂, h₁, hud, mul_one]
  have h₃ := RealJacquetFrobenius.upper_mul_apply_self b.property hbInv j
  rw [show b.val.val * b.val⁻¹.val = (1 : M) from b.val.val_inv, Matrix.one_apply_eq] at h₃
  exact h₃.symm

/-- The paired root action fixes the cell representative pointwise. -/
theorem leftUnit_mul_cell_mul_rightUnit (b : B) (v : U)
    (w : Equiv.Perm (Fin (r + 1))) (i : Fin r) (t : ℝ) :
    leftUnit b w i t * (b.val * P w * v.val) * (rightUnit v i t).val = b.val * P w * v.val := by
  change ((b.val * P w) * rootUnit i (-t) * (b.val * P w)⁻¹) *
    ((b.val * P w) * v.val) * (v.val⁻¹ * rootUnit i t * v.val) = _
  calc
    _ = (b.val * P w) * (rootUnit i (-t) * rootUnit i t) * v.val := by group
    _ = _ := by rw [rootUnit_neg_mul, mul_one]

private theorem sum_rightUnit (v : U) (i : Fin r) (t : ℝ) :
    (∑ j : Fin r, (rightUnit v i t).val.val j.castSucc j.succ) = t := by
  let u : U := ⟨rootUnit i t, matrixExpUnit_rootMatrix_mem i t⟩
  let s := superdiagonalSum (R := ℝ) (n := r)
  have h : s (rightUnit v i t) = s u := by
    change s (v⁻¹ * u * v) = _
    rw [map_mul, map_mul, map_inv]
    calc
      _ = s u * ((s v)⁻¹ * s v) := by ac_rfl
      _ = _ := by rw [inv_mul_cancel, mul_one]
  have h' : (∑ j : Fin r, (rightUnit v i t).val.val j.castSucc j.succ) =
      ∑ j : Fin r, (rootUnit i t).val j.castSucc j.succ := congrArg Multiplicative.toAdd h
  rw [h', rootUnit, matrixExpUnit_rootMatrix_val, Finset.sum_eq_single i]
  · simp only [Matrix.add_apply, Matrix.one_apply_ne i.castSucc_lt_succ.ne,
      zero_add, Matrix.smul_apply, rootMatrix_apply, true_and, ite_true, smul_eq_mul, mul_one]
  · intro j _ hj
    have hij : i.castSucc ≠ j.castSucc := fun h => hj (Fin.castSucc_injective _ h).symm
    simp [Matrix.one_apply_ne j.castSucc_lt_succ.ne, rootMatrix_apply, hij]
  · simp

/-- The right member of the stabilizer has the unipotent character of the
adjacent root, independent of the cell representative. -/
theorem character_rightUnit (a : ℝˣ) (v : U) (i : Fin r) (t : ℝ) :
    realWhittakerCharacter a (rightUnit v i t).val = (realScaledCharacter a).complex t :=
  congrArg (realScaledCharacter a).complex (sum_rightUnit v i t)

/-- The right character on the stabilizer has a nonzero infinitesimal value. -/
theorem hasDerivAt_character_rightUnit (a : ℝˣ) (v : U) (i : Fin r) :
    HasDerivAt (fun t => realWhittakerCharacter a (rightUnit v i t).val)
      (2 * π * (a : ℝ) * Complex.I) 0 := by
  simpa only [character_rightUnit] using hasDerivAt_realScaledCharacter a

/-- The left matrix generator of the paired root action. -/
def leftGenerator (b : B) (w : Equiv.Perm (Fin (r + 1))) (i : Fin r) : M :=
  -conjRoot (b.val * P w)⁻¹ i

/-- The right matrix generator of the paired root action. -/
def rightGenerator (v : U) (i : Fin r) : M := conjRoot v.val i

theorem leftGenerator_mul_self (b : B) (w : Equiv.Perm (Fin (r + 1))) (i : Fin r) :
    leftGenerator b w i * leftGenerator b w i = 0 := by
  rw [leftGenerator, neg_mul_neg, conjRoot_mul_self]

theorem rightGenerator_mul_self (v : U) (i : Fin r) :
    rightGenerator v i * rightGenerator v i = 0 := conjRoot_mul_self v.val i

theorem leftUnit_eq_exp (b : B) (w : Equiv.Perm (Fin (r + 1))) (i : Fin r) (t : ℝ) :
    leftUnit b w i t = matrixExpUnit (r + 1) (t • leftGenerator b w i) := by
  let g := b.val * P w
  have h := mul_matrixExpUnit_conjRoot g⁻¹ i (-t)
  have h' := congrArg (fun v : G => g * v) h
  simpa only [leftUnit, leftGenerator, rootUnit, g, ← mul_assoc, mul_inv_cancel, one_mul,
    neg_smul, smul_neg] using h'.symm

theorem rightUnit_eq_exp (v : U) (i : Fin r) (t : ℝ) :
    (rightUnit v i t).val = matrixExpUnit (r + 1) (t • rightGenerator v i) := by
  have h := mul_matrixExpUnit_conjRoot v.val i t
  have h' := congrArg (fun q : G => v.val⁻¹ * q) h
  simpa only [rightUnit, rightGenerator, rootUnit, Subgroup.coe_mul, Subgroup.coe_inv,
    ← mul_assoc, inv_mul_cancel, one_mul] using h'.symm

theorem leftUnit_val (b : B) (w : Equiv.Perm (Fin (r + 1))) (i : Fin r) (t : ℝ) :
    (leftUnit b w i t).val = 1 + t • leftGenerator b w i := by
  rw [leftUnit_eq_exp, matrixExpUnit_val, exp_smul_of_mul_self_eq_zero (leftGenerator_mul_self b w i)]

theorem rightUnit_val (v : U) (i : Fin r) (t : ℝ) :
    (rightUnit v i t).val.val = 1 + t • rightGenerator v i := by
  rw [rightUnit_eq_exp, matrixExpUnit_val, exp_smul_of_mul_self_eq_zero (rightGenerator_mul_self v i)]

private theorem lies_in_strictUpper_of_one_add (u : U) (X : M) (hu : u.val.val = 1 + X) :
    X.IsUpperTriangular ∧ ∀ i, X i i = 0 := by
  constructor
  · intro i j hij
    have h : u.val.val i j = 0 := u.property.1 hij
    have hij' : j < i := hij
    rwa [hu, Matrix.add_apply, Matrix.one_apply_ne hij'.ne', zero_add] at h
  · intro i
    have h : u.val.val i i = 1 := u.property.2 i
    rw [hu, Matrix.add_apply, Matrix.one_apply_eq, add_eq_left] at h
    exact h

theorem leftGenerator_strictUpper (b : B) (w : Equiv.Perm (Fin (r + 1))) (i : Fin r)
    (hi : w i.castSucc < w i.succ) :
    (leftGenerator b w i).IsUpperTriangular ∧ ∀ j, leftGenerator b w i j j = 0 :=
  lies_in_strictUpper_of_one_add ⟨leftUnit b w i 1, leftUnit_mem_upper b w i hi 1⟩ _
    (by simpa only [one_smul] using leftUnit_val b w i 1)

theorem rightGenerator_strictUpper (v : U) (i : Fin r) :
    (rightGenerator v i).IsUpperTriangular ∧ ∀ j, rightGenerator v i j j = 0 :=
  lies_in_strictUpper_of_one_add (rightUnit v i 1) _
    (by simpa only [one_smul] using rightUnit_val v i 1)

theorem sum_rightGenerator (v : U) (i : Fin r) :
    (∑ j : Fin r, rightGenerator v i j.castSucc j.succ) = 1 := by
  have h := sum_rightUnit v i 1
  simpa only [rightUnit_val, one_smul, Matrix.add_apply,
    Matrix.one_apply_ne (Fin.castSucc_lt_succ.ne), zero_add] using h

theorem hasDerivAt_pairedAction (b : B) (v : U)
    (w : Equiv.Perm (Fin (r + 1))) (i : Fin r) (X : M) :
    HasDerivAt (fun t => (leftUnit b w i t).val * X * (rightUnit v i t).val.val)
      (leftGenerator b w i * X + X * rightGenerator v i) 0 := by
  simp_rw [leftUnit_val, rightUnit_val]
  have h₁ := ((hasDerivAt_id (0 : ℝ)).smul_const (leftGenerator b w i)).const_add (1 : M)
  have h₂ := ((hasDerivAt_id (0 : ℝ)).smul_const (rightGenerator v i)).const_add (1 : M)
  simpa only [id_eq, zero_smul, zero_add, add_zero, one_smul, one_mul, mul_one] using
    (h₁.mul_const X).fun_mul h₂

/-- The ambient matrix direction of the paired root action is nilpotent. -/
theorem isNilpotent_pairedGenerator (b : B) (v : U)
    (w : Equiv.Perm (Fin (r + 1))) (i : Fin r) :
    IsNilpotent (LinearMap.mulLeft ℝ (leftGenerator b w i) +
      LinearMap.mulRight ℝ (rightGenerator v i)) := by
  have hc : Commute (LinearMap.mulLeft ℝ (leftGenerator b w i))
      (LinearMap.mulRight ℝ (rightGenerator v i)) := by
    apply LinearMap.ext
    intro x
    exact (Matrix.mul_assoc (leftGenerator b w i) x (rightGenerator v i)).symm
  exact hc.isNilpotent_add ((LinearMap.isNilpotent_mulLeft_iff ℝ _).mpr
    ⟨2, by rw [pow_two, leftGenerator_mul_self]⟩)
    ((LinearMap.isNilpotent_mulRight_iff ℝ _).mpr ⟨2, by rw [pow_two, rightGenerator_mul_self]⟩)

/-- Every lower Bruhat cell admits a paired simple-root stabilizer with an
upper unipotent left factor, a character-detecting right factor, and a
nilpotent ambient matrix action at first order. -/
def RealBruhatRootStabilizerStatement : Prop :=
  ∀ (r : ℕ) (w : Equiv.Perm (Fin (r + 1))), w ≠ Fin.revPerm →
  ∀ (g : Langlands.GeneralLinear (r + 1) ℝ), g ∈ upperBruhatCell (r + 1) ℝ w →
  ∃ (i : Fin r) (b : upperTriangularSubgroup (r + 1) ℝ) (v : upperUnipotent (r + 1) ℝ),
    g = b.val * permutation (r + 1) ℝ w * v.val ∧
    (∀ t, leftUnit b w i t ∈ upperUnipotent (r + 1) ℝ ∧
      leftUnit b w i t * g * (rightUnit v i t).val = g ∧
      ∀ a : ℝˣ, realWhittakerCharacter a (rightUnit v i t).val = (realScaledCharacter a).complex t) ∧
    IsNilpotent (LinearMap.mulLeft ℝ (leftGenerator b w i) +
      LinearMap.mulRight ℝ (rightGenerator v i))

theorem realBruhatRootStabilizer : RealBruhatRootStabilizerStatement := by
  intro r w hw g hg
  obtain ⟨i, hi⟩ := exists_adjacent_ascent w hw
  obtain ⟨⟨b, v⟩, h⟩ := upperBruhatCellMap_surjective w ⟨g, hg⟩
  have hval : b.val * permutation (r + 1) ℝ w * v.val = g := congrArg Subtype.val h
  let v₀ : upperUnipotent (r + 1) ℝ := ⟨v.val, v.property.1⟩
  refine ⟨i, b, v₀, hval.symm, fun t => ⟨leftUnit_mem_upper b w i hi t, ?_, fun a =>
    character_rightUnit a v₀ i t⟩, isNilpotent_pairedGenerator b v₀ w i⟩
  rw [← hval]
  exact leftUnit_mul_cell_mul_rightUnit b v₀ w i t

end Langlands.Global.RankinSelbergGlobal.RealBruhatRootStabilizer
