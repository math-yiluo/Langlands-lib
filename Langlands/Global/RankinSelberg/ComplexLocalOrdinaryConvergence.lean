import Langlands.Global.RankinSelberg.ComplexLocalIwasawaMeasure
import Langlands.Global.RankinSelberg.ComplexLocalUnequalKernels
import Langlands.Global.RankinSelberg.RealEqualConvergence
import Langlands.Global.RankinSelberg.StandardCompactPadding
import Langlands.Representation.Archimedean.ComplexBlockModulusBound

/-! # Absolute convergence of the original complex unequal-rank integral -/

noncomputable section
open MeasureTheory
open scoped Classical ENNReal NNReal
open Langlands.Archimedean (unitaryCompact)
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal

attribute [local instance] ArchimedeanLocal.archimedeanComplexGLMeasurable
  ArchimedeanLocal.archimedeanComplexGLBorel ArchimedeanLocal.archimedeanComplexNMeasurable
  ArchimedeanLocal.archimedeanComplexNBorel ArchimedeanLocal.archimedeanComplexQMeasurable
  ArchimedeanLocal.archimedeanComplexQBorel

namespace ComplexLocalOrdinaryConvergence

open ArchimedeanLocal ComplexLocalIwasawa
open ComplexLocalWhittakerGauge (logTorus logTorus_val)
open RealConvergenceAnalysis (rootPos rootPos_nonneg sub_last_le
  norm_cexp_mul_ofReal lintegral_exp_neg_mul_sum_abs_lt_top)

private def logPad {m n : ℕ} (y : Fin m → ℝ) (j : Fin n) : ℝ :=
  if hj : j.val < m then y ⟨j.val, hj⟩ else 0

private theorem logTorus_pad {m n : ℕ} (h : m ≤ n) (y : Fin m → ℝ) :
    padGL h (logTorus y) = logTorus (logPad (n := n) y) := by
  apply Units.ext
  ext i j
  rw [Unfolding.padGL_apply, logTorus_val, logTorus_val]
  by_cases hij : i = j
  · subst j
    by_cases hi : i.val < m
    · simp [logPad, hi]
    · simp [logPad, hi]
  · have hne : ∀ (hi : i.val < m) (hj : j.val < m),
        (⟨i.val, hi⟩ : Fin m) ≠ ⟨j.val, hj⟩ :=
      fun _ _ he => hij (Fin.ext (congrArg (fun j : Fin m => j.val) he))
    by_cases hi : i.val < m <;> by_cases hj : j.val < m <;>
      simp [hi, hj, hij, hne]

private theorem sum_abs_logPad {m n : ℕ} (h : m ≤ n) (y : Fin m → ℝ) :
    ∑ j : Fin n, |logPad y j| = ∑ j : Fin m, |y j| := by
  let e := Fin.castLEEmb h
  calc
    _ = ∑ j ∈ Finset.univ.map e, |logPad y j| :=
      (Finset.sum_subset (Finset.subset_univ _) fun j _ hj => by
        have hlt : ¬ j.val < m := by
          intro hj'
          apply hj
          exact Finset.mem_map.mpr ⟨⟨j.val, hj'⟩, Finset.mem_univ _, Fin.ext rfl⟩
        simp [logPad, hlt]).symm
    _ = _ := by
      rw [Finset.sum_map]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [logPad, e]

private theorem sum_positive_le_rootPos {r t : ℕ} (h : t < r) (y : Fin (t + 1) → ℝ) :
    ∑ j, max (y j) 0 ≤ ((t : ℝ) + 1) * rootPos (logPad (n := r + 1) y) := by
  let Y := logPad (n := r + 1) y
  have hlast : Y (Fin.last r) = 0 := by
    simp [Y, logPad, show ¬ r < t + 1 by omega]
  have hy (j : Fin (t + 1)) : y j ≤ rootPos Y := by
    let i := Fin.castLE (Nat.succ_le_succ h.le) j
    have hi : Y i = y j := by
      have hi' : i.val < t + 1 := j.isLt
      change logPad y i = y j
      rw [logPad, dite_eq_left hi']
      rfl
    simpa only [hi, hlast, sub_zero] using sub_last_le Y i
  calc
    _ ≤ ∑ _j : Fin (t + 1), rootPos Y :=
      Finset.sum_le_sum fun j _ => max_le (hy j) (rootPos_nonneg Y)
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      rfl

theorem norm_detPower_logTorus_mul {n : ℕ} (y : Fin n → ℝ) (k : unitaryCompact ℂ n)
    (s : ℂ) :
    ‖ArchimedeanLocal.detPower complexNormalizedAbs
        (logTorus y * (k : Langlands.GeneralLinear n ℂ)) s‖ =
      Real.exp (2 * s.re * ∑ j, y j) := by
  rw [ArchimedeanLocal.detPower, norm_cexp_mul_ofReal, Units.val_mul, Matrix.det_mul, logTorus_val,
    Matrix.det_diagonal, complexNormalizedAbs, norm_mul,
    Langlands.Archimedean.ComplexBlockParabolicProof.normSq_det_unitary k.2, mul_one, norm_prod]
  simp_rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _)]
  rw [← Real.exp_sum, ← Real.exp_nat_mul, Real.log_exp]
  congr 1
  push_cast
  ring

private theorem sum_add_abs {n : ℕ} (y : Fin n → ℝ) :
    (∑ j, y j) + (∑ j, |y j|) = 2 * ∑ j, max (y j) 0 := by
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rcases le_total 0 (y j) with h | h
  · rw [abs_of_nonneg h, max_eq_left h, two_mul]
  · rw [abs_of_nonpos h, max_eq_right h, mul_zero, add_neg_cancel]

private theorem exponent_bound {r t : ℕ} (h : t < r) (y : Fin (t + 1) → ℝ)
    (L : (Fin (t + 1) → ℝ) →L[ℝ] ℝ) {A T M : ℝ} (hA : 0 ≤ A)
    (hT : A + ‖L‖ + 1 ≤ T) (hM : 2 * T * ((t : ℝ) + 1) ≤ M) :
    A * (∑ j, |y j|) - M * rootPos (logPad (n := r + 1) y) + T * (∑ j, y j) ≤
      -(∑ j, |y j|) - L y := by
  have hT0 : 0 ≤ T := (by positivity : 0 ≤ A + ‖L‖ + 1).trans hT
  have h₁ := RealEqualConvergence.linear_le L y
  have h₂ := mul_le_mul_of_nonneg_left (sum_positive_le_rootPos h y)
    (show 0 ≤ 2 * T by positivity)
  have h₃ := mul_le_mul_of_nonneg_right hM (rootPos_nonneg (logPad (n := r + 1) y))
  have hs : 0 ≤ ∑ j, |y j| := Finset.sum_nonneg fun j _ => abs_nonneg _
  have h₄ := mul_le_mul_of_nonneg_right hT hs
  have h₅ := congrArg (T * ·) (sum_add_abs y)
  nlinarith only [h₁, h₂, h₃, h₄, h₅]

open Langlands.RankinSelberg (LeftUnipotentQuotient)

variable {r t : ℕ} (h : t < r) {ds es : List LocalFactor.Archimedean.ComplexCharacterData}
  {a : ℂˣ}
local notation "GT" => Langlands.GeneralLinear (t + 1) ℂ
local notation "GR" => Langlands.GeneralLinear (r + 1) ℂ

theorem exists_integrable (D : ComplexQuotientMeasureData t) (W : complexWhittakerModel r ds a)
    (V : complexWhittakerModel t es (-a)) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → Integrable (complexUnequalIntegrand h W.val V.val s) D.measure := by
  obtain ⟨κ, L, hκL⟩ := complexIwasawaToralMeasure t D
  obtain ⟨N, hN⟩ := complexWhittakerSimpleRootMajorization r ds a W
  obtain ⟨N', hN'⟩ := complexWhittakerSimpleRootMajorization t es (-a) V
  obtain ⟨C₂, hC₂, hb₂⟩ := hN' 0 []
  let A : ℝ := (N : ℝ) + N'
  let gap : ℝ := ((r - t : ℕ) : ℝ)
  refine ⟨(A + ‖L‖ + 1 + gap) / 2, fun s hs => ?_⟩
  let T : ℝ := 2 * s.re - gap
  have hT : A + ‖L‖ + 1 ≤ T := by dsimp [T]; linarith
  obtain ⟨M, hM⟩ := exists_nat_gt (2 * T * ((t : ℝ) + 1))
  obtain ⟨C₁, hC₁, hb₁⟩ := hN M []
  let C := C₁ * C₂
  have hC := mul_nonneg hC₁ hC₂
  have hgap : (s - ((r - t : ℕ) : ℂ) / 2).re = s.re - gap / 2 := by
    rw [show ((r - t : ℕ) : ℂ) / 2 = ((gap / 2 : ℝ) : ℂ) by push_cast [gap]; rfl,
      Complex.sub_re, Complex.ofReal_re]
  have hrep (y : Fin (t + 1) → ℝ) (k : unitaryCompact ℂ (t + 1)) :
      ‖complexUnequalIntegrand h W.val V.val s (Quotient.mk _ (logTorus y * (k : GT)))‖ ≤
        C * Real.exp (-(∑ j, |y j|) - L y) := by
    let p := Nat.succ_le_succ h.le
    let K : unitaryCompact ℂ (r + 1) :=
      ⟨padGL p (k : GT), unitary_padGL p (k : GT) k.2⟩
    have hg : padGL p (logTorus y * (k : GT)) = logTorus (logPad y) * (K : GR) := by
      rw [map_mul, logTorus_pad]
    have h₁ : ‖W.val (logTorus (logPad y) * (K : GR))‖ ≤
        C₁ * Real.exp ((N : ℝ) * (∑ j, |y j|) - (M : ℝ) * rootPos (logPad (n := r + 1) y)) := by
      simpa [rootPos, sum_abs_logPad p y] using hb₁ (logPad y) K
    have h₂ : ‖V.val (logTorus y * (k : GT))‖ ≤ C₂ * Real.exp ((N' : ℝ) * ∑ j, |y j|) := by
      simpa using hb₂ y k
    rw [complexUnequalIntegrand_mk h W.2 V.2, hg, norm_mul, norm_mul, norm_detPower_logTorus_mul, hgap]
    have hd : 2 * (s.re - gap / 2) = T := by dsimp [T]; ring
    rw [hd]
    calc
      _ ≤ (C₁ * Real.exp ((N : ℝ) * (∑ j, |y j|) - (M : ℝ) * rootPos (logPad (n := r + 1) y))) *
          (C₂ * Real.exp ((N' : ℝ) * ∑ j, |y j|)) * Real.exp (T * ∑ j, y j) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul h₁ h₂ (norm_nonneg _) (by positivity)) (Real.exp_nonneg _)
      _ = C * Real.exp (A * (∑ j, |y j|) - (M : ℝ) * rootPos (logPad (n := r + 1) y) +
          T * (∑ j, y j)) := by
        calc
          _ = C * (Real.exp ((N : ℝ) * (∑ j, |y j|) -
                (M : ℝ) * rootPos (logPad (n := r + 1) y)) *
              Real.exp ((N' : ℝ) * ∑ j, |y j|) * Real.exp (T * ∑ j, y j)) := by
            dsimp only [C]
            ring
          _ = _ := by
            rw [← Real.exp_add, ← Real.exp_add]
            congr 2
            dsimp only [A]
            ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (exponent_bound h y L (by dsimp [A]; positivity) hT hM.le)) hC
  let B : (Fin (t + 1) → ℝ) → ℝ≥0∞ := fun y =>
    ENNReal.ofReal (C * Real.exp (-(∑ j, |y j|) - L y))
  have hlen : Continuous (fun y : Fin (t + 1) → ℝ => ∑ j, |y j|) :=
    continuous_finsetSum _ fun j _ => (continuous_apply j).abs
  have hBm : Measurable B :=
    ENNReal.measurable_ofReal.comp
      (continuous_const.mul (Real.continuous_exp.comp (hlen.neg.sub L.continuous))).measurable
  have hDen (y : Fin (t + 1) → ℝ) :
      ENNReal.ofReal (Real.exp (L y)) * B y =
        ENNReal.ofReal C * ENNReal.ofReal (Real.exp (-1 * ∑ j, |y j|)) := by
    dsimp [B]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul hC]
    congr 1
    rw [mul_left_comm, ← Real.exp_add]
    congr 2
    ring
  refine ⟨(continuous_complexUnequalIntegrand h W.2 V.2 s).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  calc
    _ ≤ ∫⁻ q, B (alphaQ q) ∂D.measure := by
      refine lintegral_mono fun q => ?_
      induction q using Quotient.inductionOn with
      | h g =>
        rw [alphaQ_mk, mk_eq_mk_logTorus_mul_kpart g]
        exact ENNReal.ofReal_le_ofReal (hrep (alpha g) (kpart g))
    _ = (κ : ℝ≥0∞) * ∫⁻ y, ENNReal.ofReal (Real.exp (L y)) * B y := hκL B hBm
    _ = (κ : ℝ≥0∞) * (ENNReal.ofReal C *
          ∫⁻ y : Fin (t + 1) → ℝ, ENNReal.ofReal (Real.exp (-1 * ∑ j, |y j|))) := by
        simp_rw [hDen]
        rw [lintegral_const_mul]
        exact ENNReal.measurable_ofReal.comp
          (Real.continuous_exp.comp (continuous_const.mul hlen)).measurable
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.coe_lt_top
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (lintegral_exp_neg_mul_sum_abs_lt_top one_pos))

end ComplexLocalOrdinaryConvergence

open ArchimedeanLocal

/-- Absolute convergence on a right half-plane for the original kernel on the exact complex
unipotent quotient, for all vectors of the two published models. -/
def ComplexLocalOrdinaryConvergenceStatement : Prop :=
  ∀ {r t : ℕ} (h : t < r) (ds es : List LocalFactor.Archimedean.ComplexCharacterData)
    (a : ℂˣ) (D : ComplexQuotientMeasureData t) (W : complexWhittakerModel r ds a)
    (V : complexWhittakerModel t es (-a)),
      ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
        Integrable (complexUnequalIntegrand h W.val V.val s) D.measure

theorem complexLocalOrdinaryConvergence : ComplexLocalOrdinaryConvergenceStatement :=
  fun h _ _ _ D W V => ComplexLocalOrdinaryConvergence.exists_integrable h D W V

end Langlands.Global.RankinSelbergGlobal
