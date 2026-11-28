import Langlands.HarmonicAnalysis.UnitConjugation.NilpotentApproximation
import Mathlib.Algebra.Order.Ring.Finset
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.RingTheory.Polynomial.ScaleRoots

/-! # A homogeneous size from characteristic coefficients -/

noncomputable section

namespace Langlands.HarmonicAnalysis.UnitConjugation

open Set Metric Filter Polynomial _root_.Topology
open scoped NNReal

variable {F A : Type*} [NontriviallyNormedField F] [NormedRing A] [NormedAlgebra F A]
  [FiniteDimensional F A]

private theorem leftRegularCoefficients_smul (a : F) (x : A) (i : Fin (Module.finrank F A)) :
    leftRegularCoefficients F (a • x) i = leftRegularCoefficients F x i * a ^ (Module.finrank F A - i.val) := by
  by_cases ha : a = 0
  · subst a
    have hz : leftRegularCoefficients F (0 : A) = 0 :=
      (leftRegularCoefficients_eq_zero_iff (F := F) 0).mpr IsNilpotent.zero
    simp only [zero_smul, hz, Pi.zero_apply, zero_pow (Nat.sub_pos_of_lt i.isLt).ne', mul_zero]
  classical
  let b := Module.finBasis F A
  let M := LinearMap.toMatrix b b (Algebra.lmul F A x)
  have hMatrix : LinearMap.toMatrix b b (Algebra.lmul F A (a • x)) = a • M := by
    rw [map_smul, map_smul]
  have hScale : (a • M).charpoly = M.charpoly.scaleRoots a := by
    apply Polynomial.funext
    intro z
    let t := a⁻¹ * z
    have hzt : a * t = z := mul_inv_cancel_left₀ ha z
    rw [← hzt]
    have hs : Matrix.scalar _ (a * t) = a • Matrix.scalar (Fin (Module.finrank F A)) t := by
      ext i j
      by_cases hij : i = j <;> simp [Matrix.scalar, hij, smul_eq_mul]
    rw [Matrix.eval_charpoly, scaleRoots_eval_mul, Matrix.eval_charpoly,
      hs, ← smul_sub, Matrix.det_smul, Matrix.charpoly_natDegree_eq_dim]
  change (Algebra.lmul F A (a • x)).charpoly.coeff i = (Algebra.lmul F A x).charpoly.coeff i * _
  rw [← LinearMap.charpoly_toMatrix _ b, ← LinearMap.charpoly_toMatrix _ b, hMatrix,
    hScale, coeff_scaleRoots, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]

private def characteristicWeight (i : Fin (Module.finrank F A)) : ℕ :=
  Module.finrank F A - i.val

omit [FiniteDimensional F A] in
private theorem characteristicWeight_pos (i : Fin (Module.finrank F A)) :
    0 < characteristicWeight i := Nat.sub_pos_of_lt i.isLt

private def weightedCoefficientNorm (x : A) (i : Fin (Module.finrank F A)) : ℝ≥0 :=
  ‖leftRegularCoefficients F x i‖₊ ^ (1 / (characteristicWeight i : ℝ))

/-- The largest subleading coefficient norm of the left regular characteristic
polynomial, with each coefficient raised to the reciprocal of its degree. -/
def characteristicSize (F : Type*) [NontriviallyNormedField F] [NormedAlgebra F A]
    [FiniteDimensional F A] (x : A) : ℝ≥0 :=
  Finset.univ.sup (weightedCoefficientNorm (F := F) x)

omit [FiniteDimensional F A] in
private theorem characteristicWeight_root_pow (t : ℝ≥0) (i : Fin (Module.finrank F A)) :
    (t ^ characteristicWeight i) ^ (1 / (characteristicWeight i : ℝ)) = t := by
  have hp : 0 < (characteristicWeight i : ℝ) := by exact_mod_cast characteristicWeight_pos i
  rw [← NNReal.rpow_natCast, ← NNReal.rpow_mul]
  rw [mul_one_div_cancel hp.ne', NNReal.rpow_one]

@[simp]
theorem characteristicSize_smul (a : F) (x : A) :
    characteristicSize F (a • x) = ‖a‖₊ * characteristicSize F x := by
  unfold characteristicSize
  rw [Finset.mul_sup₀]
  apply Finset.sup_congr rfl
  intro i _
  rw [weightedCoefficientNorm, leftRegularCoefficients_smul, nnnorm_mul, nnnorm_pow,
    NNReal.mul_rpow, ← characteristicWeight, characteristicWeight_root_pow,
    mul_comm, ← weightedCoefficientNorm]

@[simp]
theorem characteristicSize_conjugation (g : Aˣ) (x : A) :
    characteristicSize F (conjugationHomeomorph g x) = characteristicSize F x := by
  unfold characteristicSize
  apply Finset.sup_congr rfl
  intro i _
  rw [weightedCoefficientNorm, weightedCoefficientNorm, leftRegularCoefficients_conjugation]

@[simp]
theorem characteristicSize_eq_zero_iff (x : A) : characteristicSize F x = 0 ↔ IsNilpotent x := by
  rw [← leftRegularCoefficients_eq_zero_iff (F := F), le_antisymm_iff, and_iff_left (zero_le : (0 : ℝ≥0) ≤ characteristicSize F x),
    characteristicSize, Finset.sup_le_iff]
  constructor
  · intro hx
    funext i
    apply nnnorm_eq_zero.mp
    have h := le_antisymm (hx i (Finset.mem_univ i)) (zero_le : (0 : ℝ≥0) ≤ weightedCoefficientNorm x i)
    have hp : 0 < (1 / (characteristicWeight i : ℝ)) := by positivity [characteristicWeight_pos i]
    exact (NNReal.rpow_eq_zero hp.ne').mp h
  · intro hx i _
    have hi := congrFun hx i
    have hp : 0 < (1 / (characteristicWeight i : ℝ)) := by positivity [characteristicWeight_pos i]
    rw [weightedCoefficientNorm, hi, Pi.zero_apply, nnnorm_zero, NNReal.zero_rpow hp.ne']

/-- A coefficient size at most one bounds every characteristic coefficient by one. -/
theorem norm_charpoly_coeff_le_one_of_characteristicSize (x : A)
    (hx : characteristicSize F x ≤ 1) (i : ℕ) :
    ‖(Algebra.lmul F A x).charpoly.coeff i‖ ≤ 1 := by
  by_cases hi : i < Module.finrank F A
  · let j : Fin (Module.finrank F A) := ⟨i, hi⟩
    have hp : 0 < (1 / (characteristicWeight j : ℝ)) := by positivity [characteristicWeight_pos j]
    have hw : weightedCoefficientNorm (F := F) x j ≤ 1 := (Finset.le_sup (Finset.mem_univ j)).trans hx
    have hAt : ‖leftRegularCoefficients F x j‖₊ ≤ 1 :=
      (NNReal.rpow_le_rpow_iff hp).mp (by simpa only [NNReal.one_rpow, weightedCoefficientNorm] using hw)
    exact hAt
  · have hdeg := LinearMap.charpoly_natDegree (Algebra.lmul F A x)
    rcases eq_or_lt_of_le (le_of_not_gt hi) with hj | hj
    · rw [← hj, ← hdeg, (LinearMap.charpoly_monic _).coeff_natDegree, norm_one]
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hdeg.symm ▸ hj), norm_zero]
      exact zero_le_one

/-- The coefficient size is continuous and locally constant off the nilpotent cone. -/
def CharacteristicSizeStatement (F : Type*) [NontriviallyNormedField F] [CompleteSpace F]
    [IsUltrametricDist F] [NormedAlgebra F A] [FiniteDimensional F A] : Prop :=
  Continuous (characteristicSize (A := A) F) ∧
    ∀ x : A, 0 < characteristicSize F x → ∀ᶠ y in 𝓝 x, characteristicSize F y = characteristicSize F x

variable [CompleteSpace F]

private theorem continuous_weightedCoefficientNorm (i : Fin (Module.finrank F A)) :
    Continuous (fun x : A => weightedCoefficientNorm x i) := by
  apply (NNReal.continuous_rpow_const (y := 1 / (characteristicWeight i : ℝ)) (by positivity)).comp
  exact continuous_nnnorm.comp ((continuous_apply i).comp continuous_leftRegularCoefficients)

theorem continuous_characteristicSize : Continuous (characteristicSize (A := A) F) :=
  Continuous.finset_sup_apply fun i _ => continuous_weightedCoefficientNorm i

variable [IsUltrametricDist F]

set_option maxHeartbeats 1800000 in
theorem characteristicSize_spec : CharacteristicSizeStatement (A := A) F := by
  refine ⟨continuous_characteristicSize, fun x hx => ?_⟩
  let q := characteristicSize F x
  have hWeight (i : Fin (Module.finrank F A)) : ∀ᶠ y : A in 𝓝 x,
      weightedCoefficientNorm y i ≤ q ∧ weightedCoefficientNorm x i ≤ characteristicSize F y := by
    let c : A → F := fun y => leftRegularCoefficients F y i
    by_cases hxi : c x = 0
    · have hp : 0 < (1 / (characteristicWeight i : ℝ)) := by positivity [characteristicWeight_pos i]
      have h0 : weightedCoefficientNorm x i = 0 := by
        rw [weightedCoefficientNorm, show leftRegularCoefficients F x i = 0 from hxi,
          nnnorm_zero, NNReal.zero_rpow hp.ne']
      have hOpen : IsOpen {y : A | weightedCoefficientNorm y i < q} :=
        isOpen_lt (continuous_weightedCoefficientNorm i) continuous_const
      filter_upwards [hOpen.mem_nhds (show weightedCoefficientNorm x i < q from h0.symm ▸ hx)] with y hy
      exact ⟨hy.le, h0.symm ▸ (zero_le : (0 : ℝ≥0) ≤ characteristicSize F y)⟩
    · have hc : Continuous c := (continuous_apply i).comp continuous_leftRegularCoefficients
      have hr : 0 < ‖c x‖ := norm_pos_iff.mpr hxi
      filter_upwards [hc.continuousAt.eventually_mem (ball_mem_nhds (c x) hr)] with y hy
      have hlt : ‖c y - c x‖ < ‖c x‖ := by simpa only [mem_ball, dist_eq_norm] using hy
      have hNorm : ‖c y‖ = ‖c x‖ := calc
        _ = ‖(c y - c x) + c x‖ := congrArg norm (sub_add_cancel _ _).symm
        _ = _ := by rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne, max_eq_right hlt.le]
      have hEq : weightedCoefficientNorm y i = weightedCoefficientNorm x i :=
        congrArg (fun r : ℝ≥0 => r ^ (1 / (characteristicWeight i : ℝ))) (Subtype.ext hNorm)
      refine ⟨?_, ?_⟩
      · rw [hEq]
        exact Finset.le_sup (Finset.mem_univ i)
      · rw [← hEq]
        exact Finset.le_sup (Finset.mem_univ i)
  filter_upwards [Filter.eventually_all.mpr hWeight] with y hy
  exact le_antisymm (Finset.sup_le fun i _ => (hy i).1) (Finset.sup_le fun i _ => (hy i).2)

end Langlands.HarmonicAnalysis.UnitConjugation
