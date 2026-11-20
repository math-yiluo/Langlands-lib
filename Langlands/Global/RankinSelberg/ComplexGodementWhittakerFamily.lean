import Langlands.Analysis.DominatedHolomorphicIntegral
import Langlands.Global.RankinSelberg.ComplexGodementWhittakerIntegral

/-! # Local uniform domination of the complex Godement Whittaker integral -/

noncomputable section

open MeasureTheory Set Filter
open scoped Classical SchwartzMap Matrix.Norms.Elementwise Topology
open Langlands.LocalFactor.Archimedean (ComplexCharacterData)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodementWhittakerFamily

open ArchimedeanLocal (complexNormalizedAbs)
open ComplexGodementWhittaker (augmentedPoint detLog inverse_log_length_le kernelBase)
open ComplexLocalIwasawa (alpha kpart npart npart_mul_logTorus_mul_kpart)
open ComplexLocalWhittakerGauge (logTorus)
open RealConvergenceAnalysis (rootPos rootPos_nonneg norm_cexp_mul_ofReal)
open Langlands.Archimedean.ComplexGeneralLinearHaarDensity
open Langlands.RankinSelberg.GLDeterminantDensity (matrixWeight)

variable {r : ℕ}
local notation "G" => Langlands.GeneralLinear (r + 1) ℂ
local notation "Square" => Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ
local notation "Rect" => Matrix (Fin (r + 1)) (Fin (r + 1 + 1)) ℂ
attribute [local instance] ArchimedeanLocal.archimedeanComplexGLMeasurable
  ArchimedeanLocal.archimedeanComplexGLBorel

/-- The logarithmic Iwasawa bound with a common growth order and arbitrary root decay. -/
def HasUniformSimpleRootBound {P : Type*} (S : Set P) (W : P → G → ℂ) : Prop :=
  ∃ N : ℕ, ∀ J : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ S, ∀ h : G,
    ‖W q h‖ ≤ C * Real.exp ((N : ℝ) * (∑ i, |alpha h i|) - (J : ℝ) * rootPos (alpha h))

private theorem detLog_eq (h : G) : detLog h = 2 * ∑ i, alpha h i := by
  let b := logTorus (alpha h) * (kpart h).val
  have he : (npart h).val * b = h := by rw [← mul_assoc, npart_mul_logTorus_mul_kpart]
  have hdet : h.val.det = b.val.det := by
    rw [← he, Units.val_mul, Matrix.det_mul, RankinSelberg.unipotent_det, one_mul]
  have hnorm := ComplexLocalOrdinaryConvergence.norm_detPower_logTorus_mul (alpha h) (kpart h) 1
  change ‖ArchimedeanLocal.detPower complexNormalizedAbs b 1‖ = _ at hnorm
  rw [ArchimedeanLocal.detPower, norm_cexp_mul_ofReal, Complex.one_re, one_mul] at hnorm
  exact Real.exp_injective (by simpa only [detLog, hdet, mul_one] using hnorm)

private theorem abs_detLog_le (h : G) : |detLog h| ≤ 2 * ∑ i, |alpha h⁻¹ i| := by
  have hinvdet : h⁻¹.val.det = h.val.det⁻¹ := by
    apply mul_left_cancel₀ h.det_ne_zero
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one,
      mul_inv_cancel₀ h.det_ne_zero]
  have hinv : detLog h⁻¹ = -detLog h := by
    rw [detLog, detLog, hinvdet, complexNormalizedAbs, norm_inv, inv_pow, Real.log_inv]
    rfl
  rw [← abs_neg (detLog h), ← hinv, detLog_eq, abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))]
  exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by norm_num)

private theorem norm_kernel (d : ComplexCharacterData) (Φ : 𝓢(Rect, ℂ)) (W : G → ℂ)
    (s : ℂ) (h : G) :
    ‖kernelBase d Φ W h * ArchimedeanLocal.detPower complexNormalizedAbs h s‖ =
      ‖W h⁻¹‖ * ‖Φ (augmentedPoint h)‖ * Real.exp ((d.exponent.re + s.re) * detLog h) := by
  have hnorm := Langlands.Archimedean.ComplexSwapJacquet.norm_character d
    (Langlands.GeneralLinear.determinant h)
  change ‖(d.character (Langlands.GeneralLinear.determinant h) : ℂ)‖ =
    ‖h.val.det‖ ^ (2 * d.exponent.re) at hnorm
  rw [Real.rpow_def_of_pos (norm_pos_iff.mpr h.det_ne_zero)] at hnorm
  unfold kernelBase ArchimedeanLocal.detPower
  rw [norm_mul, norm_mul, norm_mul, hnorm, norm_cexp_mul_ofReal, add_mul, Real.exp_add]
  rw [show Real.log ‖h.val.det‖ * (2 * d.exponent.re) = d.exponent.re * detLog h by
    rw [detLog, complexNormalizedAbs, Real.log_pow]
    norm_num
    ring]
  rw [show Real.log (complexNormalizedAbs h.val.det) = detLog h by rfl]
  ac_rfl

private def matrixTail (p : ℕ) (X : Square) : ℝ := ((1 + ‖X‖) ^ p)⁻¹

private def haarTail (p : ℕ) (h : G) : ℝ := complexNormalizedAbs h.val.det ^ (r + 1) * matrixTail p h.val

private theorem integrable_haarTail (p : ℕ) (hp : Module.finrank ℝ Square < p)
    (ν : Measure G) [ν.IsHaarMeasure] : Integrable (haarTail p) ν := by
  let U : Set Square := range (Units.val : G → Square)
  have hU : MeasurableSet U := by
    have he : U = {X : Square | X.det ≠ 0} := by
      ext X
      constructor
      · rintro ⟨h, rfl⟩
        exact Matrix.GeneralLinearGroup.det_ne_zero h
      · intro hX
        exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero X hX, rfl⟩
    rw [he]
    exact (isOpen_ne_fun continuous_id.matrix_det continuous_const).measurableSet
  have ht : Integrable (matrixTail p : Square → ℝ) (matrixLebesgue (r + 1)) := by
    have hi := integrable_one_add_norm (μ := matrixLebesgue (r + 1)) (r := (p : ℝ))
      (by exact_mod_cast hp)
    refine hi.congr (ae_of_all _ fun X => ?_)
    simp only [matrixTail, Real.rpow_neg (show 0 ≤ 1 + ‖X‖ by positivity), Real.rpow_natCast]
  let F : Square → ℂ := fun X => (complexNormalizedAbs X.det ^ (r + 1) * matrixTail p X : ℝ)
  have hi : Integrable (fun h : G => F h.val) (complexGeneralLinearHaar (r + 1)) := by
    apply (integrable_complexGeneralLinearHaar_iff F).mpr
    refine (ht.ofReal.mono_measure Measure.restrict_le_self).congr ?_
    filter_upwards [ae_restrict_mem hU] with X hX
    obtain ⟨h, rfl⟩ := hX
    have hd : complexNormalizedAbs h.val.det ≠ 0 :=
      (pow_pos (norm_pos_iff.mpr (Matrix.GeneralLinearGroup.det_ne_zero h)) _).ne'
    change (matrixTail p h.val : ℂ) = ((complexNormalizedAbs h.val.det)⁻¹ ^ (r + 1) : ℝ) •
      ((complexNormalizedAbs h.val.det ^ (r + 1) * matrixTail p h.val : ℝ) : ℂ)
    rw [Complex.real_smul, ← Complex.ofReal_mul, ← mul_assoc, ← mul_pow,
      inv_mul_cancel₀ hd, one_pow, one_mul]
  have hi' : Integrable (haarTail p) (complexGeneralLinearHaar (r + 1)) := by
    refine hi.norm.congr (ae_of_all _ fun h => ?_)
    change ‖(haarTail p h : ℂ)‖ = haarTail p h
    rw [Complex.norm_real, Real.norm_of_nonneg (by unfold haarTail matrixTail complexNormalizedAbs; positivity)]
  rw [Measure.isMulLeftInvariant_eq_smul ν (complexGeneralLinearHaar (r + 1))]
  exact hi'.smul_measure_nnreal

/-- The supremum of the zeroth-derivative Schwartz seminorms through order `j` in the weight. -/
def testSeminorm (j : ℕ) : Seminorm ℝ 𝓢(Rect, ℂ) :=
  (Finset.Iic (j, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2)

private theorem test_decay (Φ : 𝓢(Rect, ℂ)) (J p : ℕ) (h : G) :
    (1 + ‖augmentedPoint h‖) ^ J * ‖Φ (augmentedPoint h)‖ ≤
      2 ^ (J + p) * testSeminorm (J + p) Φ * matrixTail p h.val := by
  unfold matrixTail
  rw [← div_eq_mul_inv]
  refine (le_div_iff₀ (by positivity)).2 ?_
  have hn : ‖h.val‖ ≤ ‖augmentedPoint h‖ := by
    apply (Matrix.norm_le_iff (norm_nonneg _)).mpr
    intro i j
    rw [← ComplexGodementWhittaker.augmentedPoint_castSucc h i j]
    exact Matrix.norm_entry_le_entrywise_sup_norm _
  have hΦ := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (J + p, 0))
    le_rfl le_rfl Φ (augmentedPoint h)
  simp only [norm_iteratedFDeriv_zero] at hΦ
  calc
    _ ≤ (1 + ‖augmentedPoint h‖) ^ J * ‖Φ (augmentedPoint h)‖ * (1 + ‖augmentedPoint h‖) ^ p := by
      gcongr
    _ = (1 + ‖augmentedPoint h‖) ^ (J + p) * ‖Φ (augmentedPoint h)‖ := by rw [pow_add]; ring
    _ ≤ _ := hΦ

/-- A common simple-root bound gives a Haar integrable majorant at bounded real spectral
parameters. The bound uses a finite Schwartz seminorm of the test. -/
theorem exists_integrable_majorant {P : Type*} (ν : Measure G) [ν.IsHaarMeasure]
    (S : Set P) (W : P → G → ℂ) (hW : HasUniformSimpleRootBound S W)
    (d : ComplexCharacterData) (T : ℝ) (hT : 0 ≤ T) :
    ∃ j : ℕ, ∃ B : G → ℝ, Integrable B ν ∧ ∀ q ∈ S, ∀ (s : ℂ), |s.re| ≤ T →
      ∀ (Φ : 𝓢(Rect, ℂ)) (h : G),
        ‖kernelBase d Φ (W q) h * ArchimedeanLocal.detPower complexNormalizedAbs h s‖ ≤ testSeminorm j Φ * B h := by
  obtain ⟨N, hN⟩ := hW
  let n : ℝ := (r + 1 : ℕ)
  let A := (N : ℝ) + 2 * (|d.exponent.re| + T + n)
  let p := Module.finrank ℝ Square + 1
  have hn : 1 ≤ n := by dsimp [n]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le r)
  have hA : 0 ≤ A := by dsimp [A, n]; positivity
  obtain ⟨J, hJ⟩ := exists_nat_ge (A * n)
  obtain ⟨C, hC, hbound⟩ := hN J
  refine ⟨J + p, fun h => (C * n ^ J * 2 ^ (J + p)) * haarTail p h,
    (integrable_haarTail p (Nat.lt_succ_self _) ν).const_mul _, fun q hq s hs Φ h => ?_⟩
  let y := alpha h⁻¹
  let L := ∑ i, |y i|
  let R := rootPos y
  let D := Real.log (n * (1 + ‖augmentedPoint h‖))
  have hDN : 0 < n * (1 + ‖augmentedPoint h‖) := mul_pos (zero_lt_one.trans_le hn) (by positivity)
  have hD : 0 ≤ D :=
    Real.log_nonneg (one_le_mul_of_one_le_of_one_le hn (le_add_of_nonneg_right (norm_nonneg _)))
  have hR : 0 ≤ R := rootPos_nonneg _
  have hcoef : |d.exponent.re + s.re - n| ≤ |d.exponent.re| + T + n := by
    calc
      _ ≤ |d.exponent.re| + |s.re| + |n| := by
        rw [sub_eq_add_neg, ← abs_neg n]
        linarith only [abs_add_le d.exponent.re s.re, abs_add_le (d.exponent.re + s.re) (-n)]
      _ ≤ _ := by rw [abs_of_nonneg (zero_le_one.trans hn)]; gcongr
  have hdet : (d.exponent.re + s.re - n) * detLog h ≤ 2 * (|d.exponent.re| + T + n) * L := by
    refine (le_abs_self _).trans ?_
    rw [abs_mul, mul_comm (2 : ℝ), mul_assoc]
    exact mul_le_mul hcoef (abs_detLog_le h) (abs_nonneg _) (by positivity)
  have hexp : N * L - J * R + (d.exponent.re + s.re - n) * detLog h ≤ J * D := by
    have h₁ := mul_le_mul_of_nonneg_left (inverse_log_length_le h) hA
    have h₂ := mul_le_mul_of_nonneg_right hJ (add_nonneg hD hR)
    change A * L ≤ A * (n * (D + R)) at h₁
    dsimp only [A] at h₁
    nlinarith only [hdet, h₁, h₂]
  have hDpow : Real.exp (J * D) = n ^ J * (1 + ‖augmentedPoint h‖) ^ J := by
    rw [Real.exp_nat_mul, Real.exp_log hDN, mul_pow]
  have hH : Real.exp (n * detLog h) = complexNormalizedAbs h.val.det ^ (r + 1) := by
    have hpos : 0 < complexNormalizedAbs h.val.det := pow_pos (norm_pos_iff.mpr h.det_ne_zero) _
    dsimp only [n, detLog]
    rw [Real.exp_nat_mul, Real.exp_log hpos]
  rw [norm_kernel]
  calc
    _ ≤ C * Real.exp (N * L - J * R) * ‖Φ (augmentedPoint h)‖ *
        Real.exp ((d.exponent.re + s.re) * detLog h) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hbound q hq h⁻¹) (norm_nonneg _))
        (Real.exp_nonneg _)
    _ = C * ‖Φ (augmentedPoint h)‖ *
        Real.exp (N * L - J * R + (d.exponent.re + s.re - n) * detLog h) * Real.exp (n * detLog h) := by
      rw [mul_assoc (C * ‖Φ (augmentedPoint h)‖), ← Real.exp_add,
        show (N : ℝ) * L - J * R + (d.exponent.re + s.re - n) * detLog h + n * detLog h =
          (N * L - J * R) + (d.exponent.re + s.re) * detLog h by ring, Real.exp_add]
      ring
    _ ≤ C * ‖Φ (augmentedPoint h)‖ * Real.exp (J * D) * Real.exp (n * detLog h) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.exp_monotone hexp) (by positivity))
        (Real.exp_nonneg _)
    _ = C * n ^ J * ((1 + ‖augmentedPoint h‖) ^ J * ‖Φ (augmentedPoint h)‖) *
        complexNormalizedAbs h.val.det ^ (r + 1) := by rw [hDpow, hH]; ring
    _ ≤ C * n ^ J * (2 ^ (J + p) * testSeminorm (J + p) Φ * matrixTail p h.val) *
        complexNormalizedAbs h.val.det ^ (r + 1) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (test_decay Φ J p h) (by positivity))
        (by unfold complexNormalizedAbs; positivity)
    _ = _ := by unfold haarTail; ring

variable (r) in
/-- The transformed Godement integral preserves parameter holomorphy under a local uniform
simple-root bound, with a fixed Schwartz test and a holomorphic determinant exponent. -/
def ComplexGodementWhittakerFamilyStatement (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] : Prop :=
  ∀ (ν : Measure G) [ν.IsHaarMeasure] (S : Set E), IsOpen S →
    ∀ (d : ComplexCharacterData) (Φ : 𝓢(Rect, ℂ)) (W : E → G → ℂ) (s : E → ℂ),
      (∀ q, Continuous (W q)) →
      (∀ h, DifferentiableOn ℂ (fun q => W q h) S) →
      (∀ q ∈ S, ∃ δ : ℝ, 0 < δ ∧ HasUniformSimpleRootBound (Metric.ball q δ) W) →
      DifferentiableOn ℂ s S →
      let K (q : E) (h : G) := kernelBase d Φ (W q) h * ArchimedeanLocal.detPower complexNormalizedAbs h (s q)
      (∀ q ∈ S, Integrable (K q) ν) ∧ DifferentiableOn ℂ (fun q => ∫ h, K q h ∂ν) S

theorem complexGodementWhittakerFamily {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] :
    ComplexGodementWhittakerFamilyStatement r E := by
  intro ν hν S hS d Φ W s hWc hWd hWb hs
  dsimp only
  let K (q : E) (h : G) := kernelBase d Φ (W q) h * ArchimedeanLocal.detPower complexNormalizedAbs h (s q)
  change (∀ q ∈ S, Integrable (K q) ν) ∧ DifferentiableOn ℂ (fun q => ∫ h, K q h ∂ν) S
  apply Langlands.Analysis.dominatedHolomorphicIntegral ν S K
  · intro q
    have hχ : Continuous (fun h : G => (d.character (Langlands.GeneralLinear.determinant h) : ℂ)) :=
      (Units.continuous_val.comp d.character.continuous).comp
        Langlands.GeneralLinear.determinantContinuous.continuous
    have hlog : Continuous (detLog (r := r)) := by
      have h : Continuous (fun h : G => complexNormalizedAbs h.val.det) :=
        ((Units.continuous_val.matrix_det).norm).pow 2
      exact h.log (fun h => (pow_pos (norm_pos_iff.mpr h.det_ne_zero) _).ne')
    exact ((((Φ.continuous.comp ComplexGodementWhittaker.continuous_augmentedPoint).mul
      ((hWc q).comp continuous_inv)).mul hχ).mul
      ((Complex.continuous_ofReal.comp hlog).const_mul (s q)).cexp).aestronglyMeasurable
  · refine ae_of_all _ fun h => ?_
    have hd : DifferentiableOn ℂ (fun q => ArchimedeanLocal.detPower complexNormalizedAbs h (s q)) S :=
      (hs.mul_const _).cexp
    exact (((differentiableOn_const (c := Φ (augmentedPoint h))).mul (hWd h⁻¹)).mul_const _).mul hd
  · intro q hq
    obtain ⟨δ, hδ, hB⟩ := hWb q hq
    let T := |(s q).re| + 1
    have hT : 0 ≤ T := by dsimp [T]; positivity
    have hc := (hs.differentiableAt (hS.mem_nhds hq)).continuousAt
    have hcont : ContinuousAt (fun z => |(s z).re|) q :=
      (Complex.continuous_re.continuousAt.comp hc).abs
    have hT' : ∀ᶠ z in 𝓝 q, |(s z).re| < T :=
      hcont.eventually_lt continuousAt_const (lt_add_one _)
    have hqS : ∀ᶠ z in 𝓝 q, z ∈ S := hS.mem_nhds hq
    have hqδ : ∀ᶠ z in 𝓝 q, z ∈ Metric.ball q δ := Metric.ball_mem_nhds q hδ
    have hev := hqS.and (hqδ.and hT')
    obtain ⟨ε, hε, hεsub⟩ := Metric.eventually_nhds_iff_ball.mp hev
    obtain ⟨j, B, hBi, hBd⟩ := exists_integrable_majorant ν _ W hB d T hT
    refine ⟨ε / 2, by positivity, ?_, fun h => testSeminorm j Φ * B h,
      hBi.const_mul _, ae_of_all _ fun h z hz => ?_⟩
    · intro z hz
      rw [show 2 * (ε / 2) = ε by ring] at hz
      exact (hεsub z hz).1
    · rw [show 2 * (ε / 2) = ε by ring] at hz
      obtain ⟨_, hzδ, hzT⟩ := hεsub z hz
      exact hBd z hzδ (s z) hzT.le Φ h

end Langlands.Global.RankinSelbergGlobal.ComplexGodementWhittakerFamily
