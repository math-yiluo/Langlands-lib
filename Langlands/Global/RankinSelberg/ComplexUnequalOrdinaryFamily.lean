import Langlands.Analysis.DominatedHolomorphicIntegral
import Langlands.Global.RankinSelberg.ComplexGodementWhittakerFamily
import Langlands.Global.RankinSelberg.ComplexUnequalFamilyKernels

/-! # Joint holomorphy of the exact ordinary unequal-rank kernel integral -/

noncomputable section
open MeasureTheory Filter Set Metric
open scoped Classical ENNReal NNReal
open Langlands.Archimedean (unitaryCompact)
open Langlands.RankinSelberg (LeftUnipotentQuotient)
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexUnequalFamily

open ArchimedeanLocal ComplexLocalIwasawa
open ComplexGodementWhittakerFamily (HasUniformSimpleRootBound)
open ComplexLocalOrdinaryConvergence (norm_detPower_logTorus_mul)
open ComplexLocalWhittakerGauge (logTorus logTorus_val)
open RealConvergenceAnalysis (rootPos rootPos_nonneg sub_last_le
  lintegral_exp_neg_mul_sum_abs_lt_top)

attribute [local instance] ArchimedeanLocal.archimedeanComplexGLMeasurable
  ArchimedeanLocal.archimedeanComplexGLBorel ArchimedeanLocal.archimedeanComplexNMeasurable
  ArchimedeanLocal.archimedeanComplexNBorel ArchimedeanLocal.archimedeanComplexQMeasurable
  ArchimedeanLocal.archimedeanComplexQBorel

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

theorem sum_add_abs {n : ℕ} (y : Fin n → ℝ) :
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

/-- A lower spectral threshold and an integrable bound uniform up to any real upper bound. -/
def HalfPlaneDomination {P Q : Type*} [MeasurableSpace Q] (μ : Measure Q)
    (S : Set P) (s : P → ℂ) (F : P → Q → ℂ) (σ : ℝ) : Prop :=
  ∀ τ : ℝ, ∃ B : Q → ℝ, Integrable B μ ∧
    ∀ p ∈ S, σ < (s p).re → (s p).re ≤ τ → ∀ x, ‖F p x‖ ≤ B x

/-- On the strict spectral half-plane, uniform bounds on real intervals permit holomorphic
integration. -/
theorem differentiableOn_integral_of_halfPlaneDomination {E Q : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] [MeasurableSpace Q]
    {μ : Measure Q} {S : Set E} {s : E → ℂ} {F : E → Q → ℂ} {σ : ℝ}
    (hS : IsOpen S) (hs : Differentiable ℂ s)
    (hM : ∀ p, AEStronglyMeasurable (F p) μ)
    (hD : ∀ x, DifferentiableOn ℂ (F · x) S)
    (hB : HalfPlaneDomination μ S s F σ) :
    (∀ p ∈ S ∩ {v | σ < (s v).re}, Integrable (F p) μ) ∧
      DifferentiableOn ℂ (fun p => ∫ x, F p x ∂μ) (S ∩ {v | σ < (s v).re}) := by
  let U : Set E := S ∩ {v | σ < (s v).re}
  have hopen : IsOpen U :=
    hS.inter (isOpen_lt continuous_const (Complex.continuous_re.comp hs.continuous))
  apply Langlands.Analysis.dominatedHolomorphicIntegral (E := E) (α := Q) μ U F hM
  · exact ae_of_all _ fun x => (hD x).mono inter_subset_left
  · intro p hp
    let τ := (s p).re + 1
    have hupper : IsOpen {v : E | (s v).re < τ} :=
      isOpen_lt (Complex.continuous_re.comp hs.continuous) continuous_const
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
      ((hopen.inter hupper).mem_nhds (show p ∈ U ∩ {v | (s v).re < τ} from
        ⟨hp, by dsimp [τ]; linarith⟩))
    have hrad : 2 * (ε / 2) = ε := by ring
    obtain ⟨B, hBi, hBd⟩ := hB τ
    refine ⟨ε / 2, by positivity, ?_, B, hBi, ae_of_all _ fun x v hv => ?_⟩
    · rw [hrad]
      exact hball.trans inter_subset_left
    · rw [hrad] at hv
      obtain ⟨⟨hvs, hvσ⟩, hvτ⟩ := hball hv
      exact hBd v hvs hvσ (show (s v).re < τ from hvτ).le x

/-- The exact toral marginal integrates the majorant after its density cancels. -/
theorem integrable_toralMajorant {t : ℕ} (D : ComplexQuotientMeasureData t)
    (κ : ℝ≥0) (L : (Fin (t + 1) → ℝ) →L[ℝ] ℝ)
    (hκL : ∀ B : (Fin (t + 1) → ℝ) → ℝ≥0∞, Measurable B →
      ∫⁻ q, B (alphaQ q) ∂D.measure =
        (κ : ℝ≥0∞) * ∫⁻ y, ENNReal.ofReal (Real.exp (L y)) * B y) :
    Integrable (fun q => Real.exp (-(∑ j, |alphaQ q j|) - L (alphaQ q))) D.measure := by
  let B := fun y : Fin (t + 1) → ℝ => Real.exp (-(∑ j, |y j|) - L y)
  have hBc : Continuous B := Real.continuous_exp.comp
    ((continuous_finsetSum _ fun j _ => (continuous_apply j).abs).neg.sub L.continuous)
  refine ⟨(hBc.comp continuous_alphaQ).aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun q => Real.exp_nonneg _)).2 ?_⟩
  change (∫⁻ q, ENNReal.ofReal (B (alphaQ q)) ∂D.measure) < ⊤
  have hscale (y : Fin (t + 1) → ℝ) :
      ENNReal.ofReal (Real.exp (L y)) * ENNReal.ofReal (B y) =
        ENNReal.ofReal (Real.exp (-1 * ∑ j, |y j|)) := by
    dsimp [B]
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
    congr 2
    ring
  calc
    _ = (κ : ℝ≥0∞) * ∫⁻ y, ENNReal.ofReal (Real.exp (L y)) * ENNReal.ofReal (B y) :=
      hκL (fun y => ENNReal.ofReal (B y)) (ENNReal.measurable_ofReal.comp hBc.measurable)
    _ < ⊤ := by
      simp_rw [hscale]
      exact ENNReal.mul_lt_top ENNReal.coe_lt_top (lintegral_exp_neg_mul_sum_abs_lt_top one_pos)

/-- The exact shifted determinant factor is entire in the spectral argument. -/
theorem differentiable_detPower_parameter {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {n : ℕ} (g : Langlands.GeneralLinear n ℂ) {s : E → ℂ} (hs : Differentiable ℂ s) (c : ℂ) :
    Differentiable ℂ (fun p => ArchimedeanLocal.detPower complexNormalizedAbs g (s p - c)) :=
  Complex.differentiable_exp.comp ((hs.sub_const c).mul_const _)

section Ordinary

variable {r t : ℕ} (h : t < r) {a : ℂˣ}
local notation "GT" => Langlands.GeneralLinear (t + 1) ℂ
local notation "GR" => Langlands.GeneralLinear (r + 1) ℂ

/-- Uniform simple-root bounds give common majorants for the ordinary kernel on intervals
of the real part of the spectral variable. -/
theorem ordinary_halfPlaneDomination {P : Type*} (D : ComplexQuotientMeasureData t)
    (S : Set P) (W : P → GR → ℂ) (V : P → GT → ℂ) (s : P → ℂ)
    (hW : ∀ p, HasLeftCharacter a (W p)) (hV : ∀ p, HasLeftCharacter (-a) (V p))
    (hWb : HasUniformSimpleRootBound S W) (hVb : HasUniformSimpleRootBound S V) :
    ∃ σ, HalfPlaneDomination D.measure S s
      (fun p => complexUnequalIntegrand h (W p) (V p) (s p)) σ := by
  obtain ⟨κ, L, hκL⟩ := complexIwasawaToralMeasure t D
  obtain ⟨N, hN⟩ := hWb
  obtain ⟨N', hN'⟩ := hVb
  obtain ⟨C₂, hC₂, hb₂⟩ := hN' 0
  let A : ℝ := (N : ℝ) + N'
  let gap : ℝ := ((r - t : ℕ) : ℝ)
  let σ : ℝ := (A + ‖L‖ + 1 + gap) / 2
  refine ⟨σ, fun τ => ?_⟩
  obtain ⟨M, hM⟩ := exists_nat_gt (2 * (2 * τ - gap) * ((t : ℝ) + 1))
  obtain ⟨C₁, hC₁, hb₁⟩ := hN M
  let C := C₁ * C₂
  have hC := mul_nonneg hC₁ hC₂
  refine ⟨fun q => C * Real.exp (-(∑ j, |alphaQ q j|) - L (alphaQ q)),
    (integrable_toralMajorant D κ L hκL).const_mul C, fun v hv hvσ hvτ q => ?_⟩
  let T : ℝ := 2 * (s v).re - gap
  have hT : A + ‖L‖ + 1 ≤ T := by dsimp [T, σ] at *; linarith
  have hMT : 2 * T * ((t : ℝ) + 1) ≤ M := by
    refine le_trans ?_ hM.le
    exact mul_le_mul_of_nonneg_right (by dsimp [T]; linarith) (by positivity)
  have hgap : 2 * (s v - ((r - t : ℕ) : ℂ) / 2).re = T := by
    rw [show ((r - t : ℕ) : ℂ) / 2 = ((gap / 2 : ℝ) : ℂ) by push_cast [gap]; rfl,
      Complex.sub_re, Complex.ofReal_re]
    dsimp [T]
    ring
  have hrep (y : Fin (t + 1) → ℝ) (k : unitaryCompact ℂ (t + 1)) :
      ‖complexUnequalIntegrand h (W v) (V v) (s v) (Quotient.mk _ (logTorus y * (k : GT)))‖ ≤
        C * Real.exp (-(∑ j, |y j|) - L y) := by
    let p := Nat.succ_le_succ h.le
    let K : unitaryCompact ℂ (r + 1) :=
      ⟨padGL p (k : GT), unitary_padGL p (k : GT) k.2⟩
    have hg : padGL p (logTorus y * (k : GT)) = logTorus (logPad y) * (K : GR) := by
      rw [map_mul, logTorus_pad]
    have hα₁ : alpha (logTorus (logPad y) * (K : GR)) = logPad y := by
      simpa only [OneMemClass.coe_one, one_mul] using alpha_iwasawa 1 (logPad y) K
    have hα₂ : alpha (logTorus y * (k : GT)) = y := by
      simpa only [OneMemClass.coe_one, one_mul] using alpha_iwasawa 1 y k
    have h₁ : ‖W v (logTorus (logPad y) * (K : GR))‖ ≤
        C₁ * Real.exp ((N : ℝ) * (∑ j, |y j|) - (M : ℝ) * rootPos (logPad (n := r + 1) y)) := by
      have hb := hb₁ v hv (logTorus (logPad y) * (K : GR))
      rwa [hα₁, sum_abs_logPad p y] at hb
    have h₂ : ‖V v (logTorus y * (k : GT))‖ ≤ C₂ * Real.exp ((N' : ℝ) * ∑ j, |y j|) := by
      simpa only [hα₂, Nat.cast_zero, zero_mul, sub_zero] using hb₂ v hv (logTorus y * (k : GT))
    rw [ordinaryKernel_mk h (hW v) (hV v), hg, norm_mul, norm_mul,
      norm_detPower_logTorus_mul, hgap]
    calc
      _ ≤ (C₁ * Real.exp ((N : ℝ) * (∑ j, |y j|) - (M : ℝ) * rootPos (logPad (n := r + 1) y))) *
          (C₂ * Real.exp ((N' : ℝ) * ∑ j, |y j|)) * Real.exp (T * ∑ j, y j) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul h₁ h₂ (norm_nonneg _) (by positivity)) (Real.exp_nonneg _)
      _ = C * Real.exp (A * (∑ j, |y j|) - (M : ℝ) * rootPos (logPad (n := r + 1) y) +
          T * (∑ j, y j)) := by
        have hsum : A * (∑ j, |y j|) - (M : ℝ) * rootPos (logPad (n := r + 1) y) =
            ((N : ℝ) * (∑ j, |y j|) - (M : ℝ) * rootPos (logPad (n := r + 1) y)) +
              (N' : ℝ) * ∑ j, |y j| := by dsimp [A]; ring
        rw [hsum, Real.exp_add, Real.exp_add]
        dsimp [C]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (exponent_bound h y L (by dsimp [A]; positivity) hT hMT)) hC
  induction q using Quotient.inductionOn with
  | h g =>
    dsimp only
    rw [alphaQ_mk, mk_eq_mk_logTorus_mul_kpart g]
    exact hrep (alpha g) (kpart g)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- Holomorphy and integrability of the exact ordinary unequal-rank integral, jointly in a
finite-dimensional complex parameter space. -/
def ComplexUnequalOrdinaryFamilyStatement : Prop :=
  ∀ (D : ComplexQuotientMeasureData t) (S : Set E) (W : E → GR → ℂ) (V : E → GT → ℂ)
    (s : E → ℂ), IsOpen S → Differentiable ℂ s →
    (∀ p, HasLeftCharacter a (W p)) → (∀ p, HasLeftCharacter (-a) (V p)) →
    (∀ p, Continuous (W p)) → (∀ p, Continuous (V p)) →
    (∀ g, DifferentiableOn ℂ (W · g) S) → (∀ g, DifferentiableOn ℂ (V · g) S) →
    HasUniformSimpleRootBound S W → HasUniformSimpleRootBound S V →
    ∃ σ : ℝ,
      (∀ p ∈ S ∩ {v | σ < (s v).re},
        Integrable (complexUnequalIntegrand h (W p) (V p) (s p)) D.measure) ∧
      DifferentiableOn ℂ (fun p => complexUnequalIntegral h D (W p) (V p) (s p))
        (S ∩ {v | σ < (s v).re})

theorem complexUnequalOrdinaryFamily : ComplexUnequalOrdinaryFamilyStatement (E := E) (a := a) h := by
  intro D S W V s hS hs hW hV hWc hVc hWd hVd hWb hVb
  obtain ⟨σ, hdom⟩ := ordinary_halfPlaneDomination h D S W V s hW hV hWb hVb
  refine ⟨σ, differentiableOn_integral_of_halfPlaneDomination hS hs (fun p =>
    (continuous_ordinaryKernel h (hW p) (hV p) (hWc p) (hVc p) (s p)).aestronglyMeasurable)
      (fun q => ?_) hdom⟩
  change DifferentiableOn ℂ (fun p =>
    W p (padGL (Nat.succ_le_succ h.le) q.out) * V p q.out *
      ArchimedeanLocal.detPower complexNormalizedAbs q.out (s p - ((r - t : ℕ) : ℂ) / 2)) S
  exact ((hWd _).mul (hVd _)).mul (differentiable_detPower_parameter q.out hs _).differentiableOn

end Ordinary

end Langlands.Global.RankinSelbergGlobal.ComplexUnequalFamily
