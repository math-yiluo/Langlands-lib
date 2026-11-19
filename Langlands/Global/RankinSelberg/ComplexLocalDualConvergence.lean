import Langlands.Global.RankinSelberg.ComplexLocalDualWhittakerGauge
import Langlands.Global.RankinSelberg.ComplexLocalOrdinaryConvergence
import Langlands.Global.RankinSelberg.ComplexLocalRectangularBounds
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Integral.Pi

/-! # Absolute convergence of the complex dual rectangular kernel -/

noncomputable section
open MeasureTheory
open scoped Classical ENNReal NNReal
open Langlands.Archimedean (unitaryCompact)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData)
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal

attribute [local instance] ArchimedeanLocal.archimedeanComplexGLMeasurable
  ArchimedeanLocal.archimedeanComplexGLBorel ArchimedeanLocal.archimedeanComplexNMeasurable
  ArchimedeanLocal.archimedeanComplexNBorel ArchimedeanLocal.archimedeanComplexQMeasurable
  ArchimedeanLocal.archimedeanComplexQBorel

namespace ComplexLocalDualConvergence

open ComplexLocalIwasawa ComplexLocalRectangularBounds
open ComplexLocalWhittakerGauge (logTorus)
open ComplexLocalDualWhittakerGauge (weylLong_mem_unitary)
open ComplexLocalOrdinaryConvergence (norm_detPower_logTorus_mul)
open RealConvergenceAnalysis (rootPos rootPos_nonneg lintegral_exp_neg_mul_sum_abs_lt_top)
open Langlands.RankinSelberg (rectangularMeasure)
open ArchimedeanLocal (ComplexQuotientMeasureData complexUnequalDualKernel complexUnequalDualMeasure
  complexSelfDualMeasure)

private theorem alpha_mul_unitary {n : ℕ} (g : Langlands.GeneralLinear n ℂ)
    (k : unitaryCompact ℂ n) : alpha (g * k.val) = alpha g := by
  conv_lhs => rw [← npart_mul_logTorus_mul_kpart g]
  rw [mul_assoc]
  exact alpha_iwasawa _ _ (kpart g * k)

private theorem alpha_logTorus_mul {n : ℕ} (y : Fin n → ℝ) (k : unitaryCompact ℂ n) :
    alpha (logTorus y * k.val) = y := by
  simpa only [OneMemClass.coe_one, one_mul] using alpha_iwasawa 1 y k

private theorem reindex_mem_unitary {m n : ℕ} (e : m = n) (g : Langlands.GeneralLinear m ℂ)
    (hg : g ∈ unitaryCompact ℂ m) :
    GeneralLinear.reindex (finCongr e) g ∈ unitaryCompact ℂ n := by
  subst n
  rwa [Langlands.RankinSelberg.reindex_finCongr_self]

private theorem unfoldingWeyl_mem_unitary {r t : ℕ} (h : t < r) :
    ArchimedeanLocal.unfoldingWeyl (K := ℂ) h ∈ unitaryCompact ℂ (r + 1) := by
  let w := GeneralLinear.weylLong ((r + 1) - (t + 1)) ℂ
  let g : Langlands.GeneralLinear (t + 1) ℂ := 1
  have he : GeneralLinear.blockSum (g, w) =
      Langlands.Archimedean.ComplexBlockParabolic.blockDiagGL g w := by
    apply Units.ext
    rw [Langlands.Archimedean.ComplexBlockLimit.blockDiagGL_val]
    rfl
  have hBlock : GeneralLinear.blockSum (g, w) ∈ unitaryCompact ℂ (t + 1 + ((r + 1) - (t + 1))) := by
    rw [he]
    exact Langlands.Archimedean.ComplexBlockParabolicProof.blockDiagGL_mem_unitaryCompact'
      (one_mem _) (weylLong_mem_unitary _)
  exact reindex_mem_unitary (Nat.add_sub_of_le (Nat.le_of_lt (Nat.succ_lt_succ h))) _ hBlock

private theorem lowerBlockPair_mul_right {m d : ℕ} (g k : Langlands.GeneralLinear m ℂ)
    (x : Matrix (Fin d) (Fin m) ℂ) (b : GeneralLinear.lowerTriangularSubgroup d ℂ) :
    GeneralLinear.lowerBlockPair (g * k) (x * k.val) b =
      GeneralLinear.lowerBlockPair g x b * GeneralLinear.rankInclusion d k := by
  ext i j
  refine Fin.addCases (fun i₁ => ?_) (fun i₂ => ?_) i <;>
    refine Fin.addCases (fun j₁ => ?_) (fun j₂ => ?_) j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_add, GeneralLinear.rankInclusion, Matrix.one_apply]

private theorem rectangularPoint_mul_right {r t : ℕ} (h : t < r)
    (g k : Langlands.GeneralLinear (t + 1) ℂ)
    (x : Matrix (Fin (r - (t + 1))) (Fin (t + 1)) ℂ) :
    ArchimedeanLocal.rectangularPoint h (g * k) (x * k.val) =
      ArchimedeanLocal.rectangularPoint h g x * padGL (Nat.succ_le_succ h.le) k := by
  simp only [ArchimedeanLocal.rectangularPoint, GeneralLinear.lowerBlockLocalization,
    lowerBlockPair_mul_right, map_mul]
  rw [Unfolding.reindex_rankInclusion_rankInclusion]

private theorem rectangularPoint_unitary {r t : ℕ} (h : t < r)
    (g : Langlands.GeneralLinear (t + 1) ℂ) (k : unitaryCompact ℂ (t + 1))
    (x : Matrix (Fin (r - (t + 1))) (Fin (t + 1)) ℂ) :
    ArchimedeanLocal.rectangularPoint h (g * k.val) x =
      ArchimedeanLocal.rectangularPoint h g (x * (k.val⁻¹).val) *
        padGL (Nat.succ_le_succ h.le) k.val := by
  rw [← rectangularPoint_mul_right, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]

/-! ### The rectangular factor of the majorant -/

private theorem rectangular_sigmaFinite (a : ℂˣ) (d m : ℕ) :
    SigmaFinite (rectangularMeasure (complexSelfDualMeasure a) d m) := by
  let μ := (complexSelfDualMeasure a).measure
  have : μ.IsAddHaarMeasure := (complexSelfDualMeasure a).isAddHaar
  have : SigmaFinite μ := inferInstance
  let : ∀ _ : Fin d, SigmaFinite (Measure.pi (fun _ : Fin m => μ)) :=
    fun _ => Measure.pi.sigmaFinite _
  change SigmaFinite (Measure.pi (fun _ : Fin d => Measure.pi (fun _ : Fin m => μ)))
  exact Measure.pi.sigmaFinite _

private theorem exp_logRectangleSize_lintegral_lt_top (a : ℂˣ) (d m : ℕ) :
    (∫⁻ x : Matrix (Fin d) (Fin m) ℂ,
        ENNReal.ofReal (Real.exp (-(3 * (d : ℝ) * (m : ℝ)) * logRectangleSize x))
        ∂(rectangularMeasure (complexSelfDualMeasure a) d m)) < ⊤ := by
  let μ := (complexSelfDualMeasure a).measure
  have : μ.IsAddHaarMeasure := (complexSelfDualMeasure a).isAddHaar
  let f := fun z : ℂ => Real.exp (-3 * Real.log (1 + ‖z‖ ^ 2))
  have hf : Integrable f μ := by
    have h := integrable_rpow_neg_one_add_norm_sq (μ := μ) (E := ℂ) (r := 6)
      (by norm_num [Complex.finrank_real_complex])
    refine h.congr (ae_of_all _ fun z => ?_)
    dsimp only [f]
    rw [Real.rpow_def_of_pos (by positivity)]
    congr 1
    ring
  let F := fun x : Matrix (Fin d) (Fin m) ℂ => ∏ i, ∏ j, f (x i j)
  have hF : Integrable F (rectangularMeasure (complexSelfDualMeasure a) d m) :=
    Integrable.fintype_prod (f := fun (_ : Fin d) (v : Fin m → ℂ) => ∏ j, f (v j))
      (μ := fun _ => Measure.pi (fun _ : Fin m => μ)) fun _ =>
        Integrable.fintype_prod (f := fun _ : Fin m => f) (μ := fun _ => μ) fun _ => hf
  let H := fun x : Matrix (Fin d) (Fin m) ℂ =>
    Real.exp (-(3 * (d : ℝ) * (m : ℝ)) * logRectangleSize x)
  have hHm : Continuous H :=
    Real.continuous_exp.comp (continuous_const.mul continuous_logRectangleSize)
  have hHB (x : Matrix (Fin d) (Fin m) ℂ) : ‖H x‖ ≤ F x := by
    have hx (i : Fin d) (j : Fin m) : Real.log (1 + ‖x i j‖ ^ 2) ≤ logRectangleSize x := by
      apply Real.log_le_log (by positivity)
      apply add_le_add le_rfl
      exact (Finset.single_le_sum (fun q _ => sq_nonneg ‖x i q‖) (Finset.mem_univ j)).trans
        (Finset.single_le_sum (fun p _ => Finset.sum_nonneg fun q _ => sq_nonneg ‖x p q‖)
          (Finset.mem_univ i))
    have hsum : ∑ i, ∑ j, Real.log (1 + ‖x i j‖ ^ 2) ≤
        (d : ℝ) * (m : ℝ) * logRectangleSize x := by
      calc
        _ ≤ ∑ _i : Fin d, ∑ _j : Fin m, logRectangleSize x :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hx i j
        _ = _ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
    rw [Real.norm_of_nonneg (show 0 ≤ H x from Real.exp_nonneg _)]
    dsimp only [H, F, f]
    simp_rw [← Real.exp_sum, ← Finset.mul_sum]
    apply Real.exp_monotone
    calc
      _ = (-3 : ℝ) * ((d : ℝ) * (m : ℝ) * logRectangleSize x) := by ring
      _ ≤ _ := mul_le_mul_of_nonpos_left hsum (by norm_num)
  have hi := hF.mono' hHm.aestronglyMeasurable (ae_of_all _ hHB)
  exact (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => Real.exp_nonneg _)).mp
    hi.hasFiniteIntegral

/-! ### The common half-plane and the product bound -/

private theorem exponent_bound {m : ℕ} (y : Fin (m + 1) → ℝ) (L : (Fin (m + 1) → ℝ) →L[ℝ] ℝ)
    {A₀ A₁ B T M c X R K : ℝ} (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁) (hc : 0 ≤ c)
    (hX : 0 ≤ X) (hR : 0 ≤ R) (hT : A₀ + A₁ + ‖L‖ + 1 ≤ T)
    (hM : (2 * T + A₀ + c) * K ≤ M)
    (hU : (∑ j, max (y j) 0) + X ≤ K * (1 + R)) :
    A₀ * (B + (∑ j, |y j|) + X) - M * R + A₁ * (∑ j, |y j|) + T * (∑ j, y j) ≤
      A₀ * B + (2 * T + A₀ + c) * K - (∑ j, |y j|) - L y - c * X := by
  let S := ∑ j, |y j|
  let U := ∑ j, max (y j) 0
  let H := 2 * T + A₀ + c
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hU0 : 0 ≤ U := Finset.sum_nonneg fun _ _ => le_max_right _ _
  have hT0 : 0 ≤ T := (by positivity : 0 ≤ A₀ + A₁ + ‖L‖ + 1).trans hT
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hsum : (∑ j, y j) + S = 2 * U := by
    dsimp [S, U]
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rcases le_total 0 (y j) with hj | hj
    · rw [abs_of_nonneg hj, max_eq_left hj, two_mul]
    · rw [abs_of_nonpos hj, max_eq_right hj, mul_zero, add_neg_cancel]
  have h₁ := congrArg (T * ·) hsum
  have h₂ := mul_le_mul_of_nonneg_right (show 2 * T ≤ H by dsimp [H]; linarith) hU0
  have h₃ := mul_le_mul_of_nonneg_right (show A₀ + c ≤ H by dsimp [H]; linarith) hX
  change U + X ≤ K * (1 + R) at hU
  have h₄ := mul_le_mul_of_nonneg_left hU hH
  have h₅ := mul_le_mul_of_nonneg_right hM hR
  have h₆ := mul_le_mul_of_nonneg_right hT hS
  have h₇ := RealEqualConvergence.linear_le L y
  change L y ≤ ‖L‖ * S at h₇
  change A₀ * (B + S + X) - M * R + A₁ * S + T * (∑ j, y j) ≤ A₀ * B + H * K - S - L y - c * X
  nlinarith only [h₁, h₂, h₃, h₄, h₅, h₆, h₇]

variable {r t : ℕ} (h : t < r) {ds es : List ComplexCharacterData} {a : ℂˣ}

local notation "GT" => Langlands.GeneralLinear (t + 1) ℂ
local notation "GR" => Langlands.GeneralLinear (r + 1) ℂ
local notation "Rect" => Matrix (Fin (r - (t + 1))) (Fin (t + 1)) ℂ

theorem exists_integrable (D : ComplexQuotientMeasureData t) (W : complexWhittakerModel r ds a)
    (V : complexWhittakerModel t es (-a)) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      Integrable (complexUnequalDualKernel h W.val V.val s) (complexUnequalDualMeasure (r := r) a D) := by
  obtain ⟨κ, L, hκL⟩ := complexIwasawaToralMeasure t D
  obtain ⟨B, K, hB, hK, hBK⟩ := complexLocalRectangularBounds h
  obtain ⟨N, hN⟩ := complexDualWhittakerGauge r ds a W
  obtain ⟨N', hN'⟩ := complexDualWhittakerGauge t es (-a) V
  obtain ⟨C₂, hC₂, hb₂⟩ := hN' 0
  let A₀ : ℝ := (N : ℝ) * ((r + 1 : ℕ) : ℝ)
  let A₁ : ℝ := N'
  let gap : ℝ := ((r - t : ℕ) : ℝ)
  let c : ℝ := 3 * (((r - (t + 1) : ℕ) : ℝ)) * (((t + 1 : ℕ) : ℝ))
  have hA₀ : 0 ≤ A₀ := by dsimp [A₀]; positivity
  have hA₁ : 0 ≤ A₁ := Nat.cast_nonneg _
  have hc : 0 ≤ c := by dsimp [c]; positivity
  refine ⟨(A₀ + A₁ + ‖L‖ + 1 + gap) / 2, fun s hs => ?_⟩
  let T : ℝ := 2 * s.re - gap
  let J := (2 * T + A₀ + c) * K
  have hT : A₀ + A₁ + ‖L‖ + 1 ≤ T := by dsimp [T]; linarith
  obtain ⟨M, hM⟩ := exists_nat_gt J
  obtain ⟨C₁, hC₁, hb₁⟩ := hN M
  let C := C₁ * C₂ * Real.exp (A₀ * B + J)
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg hC₁ hC₂) (Real.exp_nonneg _)
  have hgap : (s - ((r - t : ℕ) : ℂ) / 2).re = s.re - gap / 2 := by
    rw [show ((r - t : ℕ) : ℂ) / 2 = ((gap / 2 : ℝ) : ℂ) by push_cast [gap]; rfl,
      Complex.sub_re, Complex.ofReal_re]
  have hrep (y : Fin (t + 1) → ℝ) (k : unitaryCompact ℂ (t + 1)) (x : Rect) :
      ‖complexUnequalDualKernel h W.val V.val s
          (Quotient.mk _ (logTorus y * (k : GT)), x)‖ ≤
        C * (Real.exp (-(∑ j, |y j|) - L y) * Real.exp (-c * logRectangleSize x)) := by
    let g := logTorus y * (k : GT)
    let X := logRectangleSize x
    let S := ∑ j, |y j|
    let x' := x * ((k : GT)⁻¹).val
    let P := ArchimedeanLocal.rectangularPoint h (logTorus y) x'
    let R := rootPos (alpha P)
    let p := Nat.succ_le_succ h.le
    let k' : unitaryCompact ℂ (r + 1) :=
      ⟨padGL p (k : GT) * ArchimedeanLocal.unfoldingWeyl h,
        mul_mem (unitary_padGL p (k : GT) k.2) (unfoldingWeyl_mem_unitary h)⟩
    have hg : ArchimedeanLocal.rectangularPoint h g x * ArchimedeanLocal.unfoldingWeyl h =
        P * (k' : GR) := by
      rw [rectangularPoint_unitary h (logTorus y) k, mul_assoc]
    have hX : logRectangleSize x' = X := logRectangleSize_mul_unitary x k⁻¹
    obtain ⟨hlen, hU⟩ := hBK y x'
    rw [hX] at hlen hU
    have h₁' := hb₁ (P * (k' : GR))
    rw [alpha_mul_unitary P k'] at h₁'
    have h₁ : ‖ArchimedeanLocal.dualFunction (r + 1) W.val (P * (k' : GR))‖ ≤
        C₁ * Real.exp (A₀ * (B + S + X) - (M : ℝ) * R) := by
      refine h₁'.trans (mul_le_mul_of_nonneg_left (Real.exp_monotone ?_) hC₁)
      have hlen' := mul_le_mul_of_nonneg_left hlen (Nat.cast_nonneg (α := ℝ) N)
      exact sub_le_sub_right (by simpa only [A₀, mul_assoc] using hlen') _
    have h₂ : ‖ArchimedeanLocal.dualFunction (t + 1) V.val g‖ ≤ C₂ * Real.exp (A₁ * S) := by
      have hv := hb₂ g
      rw [alpha_logTorus_mul y k] at hv
      simpa only [Nat.cast_zero, zero_mul, sub_zero] using hv
    rw [complexUnequalDualKernel_mk h W.2 V.2, hg, norm_mul, norm_mul,
      norm_detPower_logTorus_mul, hgap]
    have hd : 2 * (s.re - gap / 2) = T := by dsimp [T]; ring
    rw [hd]
    have hE : A₀ * (B + S + X) - (M : ℝ) * R + A₁ * S + T * (∑ j, y j) ≤
        A₀ * B + J - S - L y - c * X :=
      exponent_bound y L hA₀ hA₁ hc (logRectangleSize_nonneg x) (rootPos_nonneg _) hT hM.le hU
    calc
      _ ≤ (C₁ * Real.exp (A₀ * (B + S + X) - (M : ℝ) * R)) *
          (C₂ * Real.exp (A₁ * S)) * Real.exp (T * ∑ j, y j) :=
        mul_le_mul_of_nonneg_right (mul_le_mul h₁ h₂ (norm_nonneg _) (by positivity))
          (Real.exp_nonneg _)
      _ = C₁ * C₂ * Real.exp (A₀ * (B + S + X) - (M : ℝ) * R + A₁ * S + T * (∑ j, y j)) := by
        rw [Real.exp_add, Real.exp_add]
        ring
      _ ≤ C₁ * C₂ * Real.exp (A₀ * B + J - S - L y - c * X) :=
        mul_le_mul_of_nonneg_left (Real.exp_monotone hE) (mul_nonneg hC₁ hC₂)
      _ = C * (Real.exp (-S - L y) * Real.exp (-c * X)) := by
        have he : A₀ * B + J - S - L y - c * X = (A₀ * B + J) + (-S - L y) + (-c * X) := by ring
        rw [he, Real.exp_add, Real.exp_add]
        dsimp only [C]
        ring
  let Bt : (Fin (t + 1) → ℝ) → ℝ≥0∞ := fun y =>
    ENNReal.ofReal (Real.exp (-(∑ j, |y j|) - L y))
  let Br : Rect → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp (-c * logRectangleSize x))
  let μ := rectangularMeasure (complexSelfDualMeasure a) (r - (t + 1)) (t + 1)
  have : SigmaFinite μ := rectangular_sigmaFinite a _ _
  have ht : Measurable Bt := ENNReal.measurable_ofReal.comp (Real.continuous_exp.comp
    ((continuous_finsetSum _ fun j _ => (continuous_apply j).abs).neg.sub L.continuous)).measurable
  have hα : Measurable (alphaQ (n := t + 1)) := continuous_alphaQ.measurable
  have hr : Measurable Br := ENNReal.measurable_ofReal.comp
    (Real.continuous_exp.comp (continuous_const.mul continuous_logRectangleSize)).measurable
  have hmul : Measurable (fun z : Langlands.RankinSelberg.LeftUnipotentQuotient t ℂ × Rect =>
      Bt (alphaQ z.1) * Br z.2) :=
    ((ht.comp hα).comp measurable_fst).mul (hr.comp measurable_snd)
  have hti : (∫⁻ q, Bt (alphaQ q) ∂D.measure) < ⊤ := by
    have hscale (y : Fin (t + 1) → ℝ) :
        ENNReal.ofReal (Real.exp (L y)) * Bt y =
          ENNReal.ofReal (Real.exp (-1 * ∑ j, |y j|)) := by
      dsimp [Bt]
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
      congr 2
      ring
    rw [hκL _ ht]
    simp_rw [hscale]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top (lintegral_exp_neg_mul_sum_abs_lt_top one_pos)
  have hri : (∫⁻ x, Br x ∂μ) < ⊤ := exp_logRectangleSize_lintegral_lt_top a _ _
  refine ⟨(continuous_complexUnequalDualKernel h W.2 V.2 s).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  change (∫⁻ z, ENNReal.ofReal ‖complexUnequalDualKernel h W.val V.val s z‖ ∂D.measure.prod μ) < ⊤
  calc
    _ ≤ ∫⁻ z, ENNReal.ofReal C * (Bt (alphaQ z.1) * Br z.2) ∂D.measure.prod μ := by
      refine lintegral_mono ?_
      rintro ⟨q, x⟩
      induction q using Quotient.inductionOn with
      | h g =>
        dsimp only [Prod.fst, Prod.snd]
        rw [alphaQ_mk, mk_eq_mk_logTorus_mul_kpart g]
        dsimp only [Bt, Br]
        rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← ENNReal.ofReal_mul hC]
        exact ENNReal.ofReal_le_ofReal (hrep (alpha g) (kpart g) x)
    _ = ENNReal.ofReal C * ((∫⁻ q, Bt (alphaQ q) ∂D.measure) * ∫⁻ x, Br x ∂μ) := by
      rw [lintegral_const_mul _ hmul]
      exact congrArg (ENNReal.ofReal C * ·)
        (lintegral_prod_mul (ht.comp hα).aemeasurable hr.aemeasurable)
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.mul_lt_top hti hri)

end ComplexLocalDualConvergence

open ArchimedeanLocal (ComplexQuotientMeasureData complexUnequalIntegrand complexUnequalDualKernel
  complexUnequalDualMeasure)

/-- Both kernels of the published complex local unequal-rank functional equation are integrable
on one right half-plane for each pair of model vectors and compatible quotient measure. -/
def ComplexLocalUnequalConvergenceStatement : Prop :=
  ∀ {r t : ℕ} (h : t < r) (ds es : List ComplexCharacterData)
    (a : ℂˣ) (D : ComplexQuotientMeasureData t) (W : complexWhittakerModel r ds a)
    (V : complexWhittakerModel t es (-a)),
      ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
        Integrable (complexUnequalIntegrand h W.val V.val s) D.measure ∧
        Integrable (complexUnequalDualKernel h W.val V.val s) (complexUnequalDualMeasure (r := r) a D)

theorem complexLocalUnequalConvergence : ComplexLocalUnequalConvergenceStatement := by
  intro r t h ds es a D W V
  obtain ⟨σ₁, h₁⟩ := complexLocalOrdinaryConvergence h ds es a D W V
  obtain ⟨σ₂, h₂⟩ := ComplexLocalDualConvergence.exists_integrable h D W V
  exact ⟨max σ₁ σ₂, fun s hs =>
    ⟨h₁ s ((le_max_left _ _).trans_lt hs), h₂ s ((le_max_right _ _).trans_lt hs)⟩⟩

end Langlands.Global.RankinSelbergGlobal
