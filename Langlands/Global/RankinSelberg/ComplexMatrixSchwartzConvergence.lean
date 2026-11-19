import Langlands.Global.RankinSelberg.ComplexPlaceFunctionalEquationReduction
import Langlands.Representation.Archimedean.ComplexGeneralLinearHaarDensity
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-! # Height-weighted Schwartz integrals on complex matrix groups -/

noncomputable section

open MeasureTheory Measure
open scoped SchwartzMap Matrix.Norms.Operator NNReal

namespace Langlands.Global.RankinSelbergGlobal.ComplexMatrixSchwartz

open Langlands.Archimedean.ComplexGeneralLinearHaarDensity
open Langlands.RankinSelberg.GLDeterminantDensity (matrixWeight)
open Function

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear n ℂ) := borel _
local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear n ℂ) := ⟨rfl⟩

private abbrev Square (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

private def entryLinear (n : ℕ) (i j : Fin n) : Square n →ₗ[ℝ] ℂ where
  toFun A := A i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem hasTemperateGrowth_entry {n : ℕ} (i j : Fin n) :
    HasTemperateGrowth (fun X : Square n => X i j) :=
  (entryLinear n i j).toContinuousLinearMap.hasTemperateGrowth

private theorem hasTemperateGrowth_det_of_entries {n : ℕ} (F : Square n → Square n)
    (hF : ∀ i j, HasTemperateGrowth (fun X => F X i j)) :
    HasTemperateGrowth (fun X => (F X).det) := by
  classical
  simp only [Matrix.det_apply']
  apply HasTemperateGrowth.sum
  intro e _
  apply (HasTemperateGrowth.const _).mul
  have hprod (S : Finset (Fin n)) : HasTemperateGrowth (fun X => ∏ i ∈ S, F X (e i) i) := by
    induction S using Finset.induction_on with
    | empty => simp only [Finset.prod_empty]; exact HasTemperateGrowth.const (1 : ℂ)
    | insert i S hi hS =>
      simp only [Finset.prod_insert hi]
      exact (hF (e i) i).mul hS
  exact hprod Finset.univ

private theorem hasTemperateGrowth_adjugate_entry {n : ℕ} (i j : Fin n) :
    HasTemperateGrowth (fun X : Square n => X.adjugate i j) := by
  classical
  simp only [Matrix.adjugate_apply]
  apply hasTemperateGrowth_det_of_entries
  intro a b
  by_cases h : a = j
  · simp only [Matrix.updateRow_apply, h, ite_true]
    exact HasTemperateGrowth.const _
  · simp only [Matrix.updateRow_apply, h, ite_false]
    exact hasTemperateGrowth_entry a b

private def entrySquareSum {n : ℕ} (X : Square n) : ℝ :=
  ∑ i, ∑ j, ‖X i j‖ ^ 2

private def detNormSq {n : ℕ} (X : Square n) : ℝ := ‖X.det‖ ^ 2

private def clearedHeight {n : ℕ} (X : Square n) : ℝ :=
  detNormSq X * entrySquareSum X + entrySquareSum X.adjugate

private theorem clearedHeight_nonneg {n : ℕ} (X : Square n) : 0 ≤ clearedHeight X := by
  unfold clearedHeight detNormSq entrySquareSum
  positivity

private theorem hasTemperateGrowth_detNormSq (n : ℕ) :
    HasTemperateGrowth (detNormSq (n := n)) :=
  (hasTemperateGrowth_norm_sq (H := ℂ)).comp
    (hasTemperateGrowth_det_of_entries id hasTemperateGrowth_entry)

private theorem hasTemperateGrowth_entrySquareSum {n : ℕ} (F : Square n → Square n)
    (hF : ∀ i j, HasTemperateGrowth (fun X => F X i j)) :
    HasTemperateGrowth (fun X => entrySquareSum (F X)) := by
  unfold entrySquareSum
  exact HasTemperateGrowth.sum fun i _ => HasTemperateGrowth.sum fun j _ =>
    (hasTemperateGrowth_norm_sq (H := ℂ)).comp (hF i j)

private theorem hasTemperateGrowth_clearedHeight (n : ℕ) :
    HasTemperateGrowth (clearedHeight (n := n)) :=
  ((hasTemperateGrowth_detNormSq n).mul
    (hasTemperateGrowth_entrySquareSum id hasTemperateGrowth_entry)).add
      (hasTemperateGrowth_entrySquareSum Matrix.adjugate hasTemperateGrowth_adjugate_entry)

private theorem clearedHeight_val {n : ℕ} (g : Langlands.GeneralLinear n ℂ) :
    clearedHeight g.val = detNormSq g.val * complexMatrixHeight g := by
  have hadj : g.val.adjugate = g.val.det • g⁻¹.val := by
    calc
      _ = g⁻¹.val * (g.val * g.val.adjugate) := by
        rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
      _ = _ := by rw [Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one]
  unfold clearedHeight entrySquareSum detNormSq complexMatrixHeight
  rw [hadj]
  simp only [Matrix.smul_apply, smul_eq_mul, norm_mul, mul_pow, Finset.sum_add_distrib,
    mul_add, Finset.mul_sum]

private theorem matrixWeight_eq_rpow {n : ℕ} {X : Square n} (hX : 0 < detNormSq X) :
    (matrixWeight n normSqHom X : ℝ) = detNormSq X ^ (-(n : ℝ)) := by
  rw [matrixWeight, NNReal.coe_pow, NNReal.coe_inv, inv_pow, Real.rpow_neg hX.le,
    Real.rpow_natCast]
  rfl

/-- A complex Schwartz matrix test times a power of the height and of the normalized
absolute determinant is absolutely integrable as soon as `Re s ≥ n + M`. -/
theorem integrable_height_schwartz_detPower (n M : ℕ) (Φ : 𝓢(Square n, ℂ)) (s : ℂ)
    (hs : (n : ℝ) + M ≤ s.re) :
    Integrable (fun g : Langlands.GeneralLinear n ℂ =>
      (complexMatrixHeight g ^ M : ℝ) * Φ g.val * ((detNormSq g.val : ℝ) : ℂ) ^ s)
      (complexGeneralLinearHaar n) := by
  let U : Set (Square n) := Set.range (Units.val : Langlands.GeneralLinear n ℂ → Square n)
  have hU : IsOpen U := Units.isOpenEmbedding_val.isOpen_range
  have hd (X : Square n) (hX : X ∈ U) : 0 < detNormSq X := by
    obtain ⟨g, rfl⟩ := hX
    exact pow_pos (norm_pos_iff.mpr (Matrix.GeneralLinearGroup.det_ne_zero g)) _
  let F (X : Square n) : ℂ := (clearedHeight X ^ M : ℝ) * Φ X * ((detNormSq X : ℝ) : ℂ) ^ (s - M)
  have hF (g : Langlands.GeneralLinear n ℂ) : F g.val =
      (complexMatrixHeight g ^ M : ℝ) * Φ g.val * ((detNormSq g.val : ℝ) : ℂ) ^ s := by
    have hdet := hd g.val ⟨g, rfl⟩
    dsimp only [F]
    rw [clearedHeight_val, mul_pow, Complex.ofReal_mul, Complex.ofReal_pow]
    let z : ℂ := detNormSq g.val
    have hz : z ≠ 0 := by
      dsimp [z]
      exact_mod_cast hdet.ne'
    calc
      _ = (complexMatrixHeight g ^ M : ℝ) * Φ g.val * (z ^ (M : ℂ) * z ^ (s - M)) := by
        rw [Complex.cpow_natCast]
        dsimp only [z]
        ring
      _ = _ := by
        rw [← Complex.cpow_add _ _ hz,
          show (M : ℂ) + (s - M) = s by ring]
  simp_rw [← hF]
  apply (integrable_complexGeneralLinearHaar_iff F).mpr
  let q : ℝ := s.re - M - n
  have hq : 0 ≤ q := by dsimp [q]; linarith
  obtain ⟨N, hN⟩ := exists_nat_ge q
  let P (X : Square n) : ℝ := clearedHeight X ^ M * (1 + detNormSq X) ^ N
  have hP : HasTemperateGrowth P :=
    ((hasTemperateGrowth_clearedHeight n).pow M).mul
      (((HasTemperateGrowth.const 1).add (hasTemperateGrowth_detNormSq n)).pow N)
  let G := SchwartzMap.smulLeftCLM ℂ P Φ
  have hG : Integrable G (matrixLebesgue n) := G.integrable
  refine (hG.norm.mono_measure Measure.restrict_le_self).mono' ?_ ?_
  · have hFcont : ContinuousOn F U :=
      (((Complex.continuous_ofReal.comp
        ((hasTemperateGrowth_clearedHeight n).1.continuous.pow M)).continuousOn.mul
        Φ.continuous.continuousOn).mul
        ((Complex.continuous_ofReal.comp (hasTemperateGrowth_detNormSq n).1.continuous).continuousOn.cpow_const
          (fun X hX => Complex.ofReal_mem_slitPlane.mpr (hd X hX))))
    exact ((Langlands.RankinSelberg.GLDeterminantDensity.measurable_matrixWeight n normSqHom
      continuous_normSqHom).aestronglyMeasurable).smul (hFcont.aestronglyMeasurable hU.measurableSet)
  · filter_upwards [ae_restrict_mem hU.measurableSet] with X hX
    have hdet := hd X hX
    have hp : 0 ≤ P X := mul_nonneg (pow_nonneg (clearedHeight_nonneg X) _)
      (pow_nonneg (by linarith) _)
    have hpow : detNormSq X ^ q ≤ (1 + detNormSq X) ^ N := by
      calc
        _ ≤ (1 + detNormSq X) ^ q := Real.rpow_le_rpow hdet.le (by linarith) hq
        _ ≤ _ := by
          rw [← Real.rpow_natCast]
          exact Real.rpow_le_rpow_of_exponent_le (by linarith) hN
    have hGN : ‖G X‖ = P X * ‖Φ X‖ := by
      change ‖SchwartzMap.smulLeftCLM ℂ P Φ X‖ = _
      rw [SchwartzMap.smulLeftCLM_apply_apply hP, norm_smul, Real.norm_eq_abs, abs_of_nonneg hp]
    change ‖(matrixWeight n normSqHom X : ℝ) • F X‖ ≤ ‖G X‖
    rw [hGN]
    calc
      _ = clearedHeight X ^ M * detNormSq X ^ q * ‖Φ X‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity),
          matrixWeight_eq_rpow hdet]
        dsimp only [F]
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (pow_nonneg (clearedHeight_nonneg X) _),
          Complex.norm_cpow_eq_rpow_re_of_pos hdet, Complex.sub_re, Complex.natCast_re]
        calc
          _ = clearedHeight X ^ M *
              (detNormSq X ^ (-(n : ℝ)) * detNormSq X ^ (s.re - M)) * ‖Φ X‖ := by ring
          _ = _ := by rw [← Real.rpow_add hdet]; congr 3; dsimp [q]; ring
      _ ≤ _ := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow
          (pow_nonneg (clearedHeight_nonneg X) _)) (norm_nonneg _)

/-- The complex Schwartz convergence clause of Jacquet's Lemma 3.3, with an explicit
sufficient threshold for the real part. -/
def ComplexMatrixSchwartzConvergenceStatement : Prop :=
  ∀ (n M : ℕ) (Φ : 𝓢(Square n, ℂ)) (s : ℂ), (n : ℝ) + M ≤ s.re →
    Integrable (fun g : Langlands.GeneralLinear n ℂ =>
      (complexMatrixHeight g ^ M : ℝ) * Φ g.val *
        ((ArchimedeanLocal.complexNormalizedAbs g.val.det : ℝ) : ℂ) ^ s)
      (complexGeneralLinearHaar n)

theorem complexMatrixSchwartzConvergence : ComplexMatrixSchwartzConvergenceStatement :=
  integrable_height_schwartz_detPower

end Langlands.Global.RankinSelbergGlobal.ComplexMatrixSchwartz
