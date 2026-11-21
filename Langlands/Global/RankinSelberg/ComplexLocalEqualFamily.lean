import Langlands.Global.RankinSelberg.ComplexUnequalOrdinaryFamily
import Langlands.Global.RankinSelberg.ComplexLastRowSchwartz
import Langlands.Global.RankinSelberg.ComplexLocalEqualQuotientChange

/-! # Holomorphy of complex equal-rank integrals in Whittaker families -/

noncomputable section

open MeasureTheory Set
open Langlands.Archimedean (unitaryCompact)
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open Langlands.QuotientIntegration (descend leftQuotientMap leftQuotient_isOpenQuotientMap)
open scoped SchwartzMap NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquet

open ArchimedeanLocal ComplexLocalIwasawa
open ComplexUnequalFamily (HasLeftCharacter HalfPlaneDomination sum_add_abs
  integrable_toralMajorant differentiableOn_integral_of_halfPlaneDomination
  differentiable_detPower_parameter)
open ComplexGodementWhittakerFamily (HasUniformSimpleRootBound)
open ComplexLocalOrdinaryConvergence (norm_detPower_logTorus_mul)
open ComplexLocalWhittakerGauge (logTorus)
open ComplexLastRowSchwartz (complexLastRowSchwartz)
open RealConvergenceAnalysis (rootPos rootPos_nonneg sub_last_le)

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

variable {r : ℕ}

local notation "n" => r + 1
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "N" => GeneralLinear.upperUnipotent n ℂ
local notation "K" => unitaryCompact ℂ n
local notation "Q" => LeftUnipotentQuotient r ℂ
local notation "Row" => Fin n → ℂ
local notation "row" => RankinSelberg.lastRow
local notation "P" => ArchimedeanLocal.detPower complexNormalizedAbs

private theorem equalFamily_invariance {a : ℂˣ} {W V : G → ℂ}
    (hW : HasLeftCharacter a W) (hV : HasLeftCharacter (-a) V)
    (φ : Row → ℂ) (s : ℂ) (u : N) (g : G) :
    W (u.val * g) * V (u.val * g) * φ (row (u.val * g)) * P (u.val * g) s =
      W g * V g * φ (row g) * P g s := by
  rw [hW u g, hV u g, mul_mul_mul_comm, ComplexCharacterChange.whittakerCharacter_neg_parameter,
    one_mul, RankinSelberg.lastRow_unipotent_mul u]
  simp only [ArchimedeanLocal.detPower, Units.val_mul, Matrix.det_mul,
    RankinSelberg.unipotent_det, one_mul]

private theorem equalFamily_kernel_mk {a : ℂˣ} {W V : G → ℂ}
    (hW : HasLeftCharacter a W) (hV : HasLeftCharacter (-a) V)
    (φ : Row → ℂ) (s : ℂ) (g : G) :
    complexEqualIntegrand W V φ s (Quotient.mk _ g) = W g * V g * φ (row g) * P g s :=
  congrArg (descend N (fun g => W g * V g * φ (row g) * P g s)
    (equalFamily_invariance hW hV φ s)) (Quotient.out_eq (Quotient.mk _ g))

private theorem equalFamily_kernel_continuous {a : ℂˣ} {W V : G → ℂ}
    (hW : HasLeftCharacter a W) (hV : HasLeftCharacter (-a) V)
    (hWc : Continuous W) (hVc : Continuous V) (φ : 𝓢(Row, ℂ)) (s : ℂ) :
    Continuous (complexEqualIntegrand W V φ s) := by
  have hq := leftQuotient_isOpenQuotientMap N
  rw [← hq.continuous_comp_iff]
  have he : complexEqualIntegrand W V φ s ∘ leftQuotientMap N =
      fun g => W g * V g * φ (row g) * P g s := funext (equalFamily_kernel_mk hW hV φ s)
  rw [he]
  have hrow : Continuous (row : G → Row) :=
    continuous_pi fun j => (GeneralLinear.entry (Fin.last r) j).continuous
  have hd : Continuous (fun g : G => complexNormalizedAbs g.val.det) :=
    Units.continuous_val.matrix_det.norm.pow 2
  have hP : Continuous (fun g : G => P g s) :=
    Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
      (hd.log fun g => pow_ne_zero 2 (norm_ne_zero_iff.mpr g.det_ne_zero))))
  exact ((hWc.mul hVc).mul (φ.continuous.comp hrow)).mul hP

private theorem sum_positive_le_last_root (y : Fin n → ℝ) :
    ∑ j, max (y j) 0 ≤ (n : ℝ) * (max (y (Fin.last r)) 0 + rootPos y) := by
  calc
    _ ≤ ∑ _j : Fin n, (max (y (Fin.last r)) 0 + rootPos y) := by
      apply Finset.sum_le_sum
      intro j _
      exact max_le (by linarith [sub_last_le y j, le_max_left (y (Fin.last r)) 0])
        (add_nonneg (le_max_right _ _) (rootPos_nonneg y))
    _ = _ := by simp [nsmul_eq_mul, mul_add]

private theorem equalFamily_exponent_bound (y : Fin n → ℝ)
    (L : (Fin n → ℝ) →L[ℝ] ℝ) {A T M : ℝ} (hA : 0 ≤ A)
    (hT : A + ‖L‖ + 1 ≤ T) (hM : 2 * T * (n : ℝ) ≤ M) :
    A * (∑ j, |y j|) + T * (∑ j, y j) -
        M * (max (y (Fin.last r)) 0 + rootPos y) ≤ -(∑ j, |y j|) - L y := by
  have hT0 : 0 ≤ T := (by positivity : 0 ≤ A + ‖L‖ + 1).trans hT
  have hpos := mul_le_mul_of_nonneg_left (sum_positive_le_last_root y) (show 0 ≤ 2 * T by positivity)
  have hdecay := mul_le_mul_of_nonneg_right hM
    (add_nonneg (le_max_right (y (Fin.last r)) 0) (rootPos_nonneg y))
  have hs : 0 ≤ ∑ j, |y j| := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hgrowth := mul_le_mul_of_nonneg_right hT hs
  have hsum := congrArg (T * ·) (sum_add_abs y)
  linarith [RealEqualConvergence.linear_le L y]

private theorem equalFamily_halfPlaneDomination {E : Type*} {a : ℂˣ}
    (D : ComplexQuotientMeasureData r) (S : Set E) (W V : E → G → ℂ)
    (s : E → ℂ) (φ : 𝓢(Row, ℂ))
    (hW : ∀ p, HasLeftCharacter a (W p)) (hV : ∀ p, HasLeftCharacter (-a) (V p))
    (hWb : HasUniformSimpleRootBound S W) (hVb : HasUniformSimpleRootBound S V) :
    ∃ σ, HalfPlaneDomination D.measure S s (fun p => complexEqualIntegrand (W p) (V p) φ (s p)) σ := by
  obtain ⟨κ, L, hκL⟩ := complexIwasawaToralMeasure r D
  obtain ⟨B, hB⟩ := hWb
  obtain ⟨B', hB'⟩ := hVb
  obtain ⟨C₂, hC₂, hb₂⟩ := hB' 0
  let A : ℝ := (B : ℝ) + B'
  let σ : ℝ := (A + ‖L‖ + 1) / 2
  refine ⟨σ, fun τ => ?_⟩
  obtain ⟨M, hM⟩ := exists_nat_gt (2 * (2 * τ) * (n : ℝ))
  obtain ⟨C₁, hC₁, hb₁⟩ := hB M
  obtain ⟨C₃, hC₃, hb₃⟩ := (complexLastRowSchwartz (r := r)) φ M
  let C := C₁ * C₂ * C₃
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg hC₁ hC₂) hC₃
  refine ⟨fun q => C * Real.exp (-(∑ j, |alphaQ q j|) - L (alphaQ q)),
    (integrable_toralMajorant D κ L hκL).const_mul C, fun p hp hpσ hpτ q => ?_⟩
  let T := 2 * (s p).re
  have hAT : A + ‖L‖ + 1 ≤ T := by dsimp [T, σ] at *; linarith
  have hTM : 2 * T * (n : ℝ) ≤ M := by
    refine le_trans ?_ hM.le
    exact mul_le_mul_of_nonneg_right (by dsimp [T]; linarith) (by positivity)
  have hrep (y : Fin n → ℝ) (k : K) :
      ‖complexEqualIntegrand (W p) (V p) φ (s p) (Quotient.mk _ (logTorus y * k.val))‖ ≤
        C * Real.exp (-(∑ j, |y j|) - L y) := by
    let g := logTorus y * k.val
    have hgα : alpha g = y := by
      simpa only [g, OneMemClass.coe_one, one_mul] using alpha_iwasawa 1 y k
    have h₁ := hb₁ p hp g
    have h₂ := hb₂ p hp g
    rw [hgα] at h₁
    simp only [hgα, Nat.cast_zero, zero_mul, sub_zero] at h₂
    rw [equalFamily_kernel_mk (hW p) (hV p), norm_mul, norm_mul, norm_mul,
      norm_detPower_logTorus_mul]
    calc
      _ ≤ (C₁ * Real.exp ((B : ℝ) * (∑ j, |y j|) - (M : ℝ) * rootPos y)) *
            (C₂ * Real.exp ((B' : ℝ) * (∑ j, |y j|))) *
            (C₃ * Real.exp (-(M : ℝ) * max (y (Fin.last r)) 0)) *
              Real.exp (T * ∑ j, y j) := by
        gcongr
        exact hb₃ y k
      _ = C * Real.exp (A * (∑ j, |y j|) + T * (∑ j, y j) -
            (M : ℝ) * (max (y (Fin.last r)) 0 + rootPos y)) := by
        rw [show A * (∑ j, |y j|) + T * (∑ j, y j) -
              (M : ℝ) * (max (y (Fin.last r)) 0 + rootPos y) =
            ((B : ℝ) * (∑ j, |y j|) - (M : ℝ) * rootPos y) +
              (B' : ℝ) * (∑ j, |y j|) + (-(M : ℝ) * max (y (Fin.last r)) 0) +
              T * (∑ j, y j) by dsimp [A]; ring]
        simp only [Real.exp_add]
        dsimp [C]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (equalFamily_exponent_bound y L (by dsimp [A]; positivity) hAT hTM)) hC
  induction q using Quotient.inductionOn with
  | h g =>
    dsimp only
    rw [alphaQ_mk, mk_eq_mk_logTorus_mul_kpart g]
    exact hrep (alpha g) (kpart g)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- On a common spectral right half-plane, uniform bounds for two Whittaker
families imply integrability and joint holomorphy of the exact equal-rank integral. -/
def ComplexLocalEqualFamilyStatement : Prop :=
  ∀ (a : ℂˣ) (D : ComplexQuotientMeasureData r) (S : Set E) (W V : E → G → ℂ)
    (s : E → ℂ) (φ : 𝓢(Row, ℂ)), IsOpen S → Differentiable ℂ s →
    (∀ p, HasLeftCharacter a (W p)) → (∀ p, HasLeftCharacter (-a) (V p)) →
    (∀ p, Continuous (W p)) → (∀ p, Continuous (V p)) →
    (∀ g, DifferentiableOn ℂ (W · g) S) → (∀ g, DifferentiableOn ℂ (V · g) S) →
    HasUniformSimpleRootBound S W → HasUniformSimpleRootBound S V →
    ∃ σ : ℝ,
      (∀ p ∈ S ∩ {v | σ < (s v).re}, Integrable (complexEqualIntegrand (W p) (V p) φ (s p)) D.measure) ∧
      DifferentiableOn ℂ (fun p => complexEqualIntegral D (W p) (V p) φ (s p))
        (S ∩ {v | σ < (s v).re})

theorem complexLocalEqualFamily : ComplexLocalEqualFamilyStatement (r := r) (E := E) := by
  intro a D S W V s φ hS hs hW hV hWc hVc hWd hVd hWb hVb
  obtain ⟨σ, hdom⟩ := equalFamily_halfPlaneDomination D S W V s φ hW hV hWb hVb
  refine ⟨σ, differentiableOn_integral_of_halfPlaneDomination hS hs (fun p =>
    (equalFamily_kernel_continuous (hW p) (hV p) (hWc p) (hVc p) φ (s p)).aestronglyMeasurable)
    (fun q => ?_) hdom⟩
  change DifferentiableOn ℂ (fun p =>
    W p q.out * V p q.out * φ (row q.out) * P q.out (s p)) S
  have hP : Differentiable ℂ (fun p => P q.out (s p)) := by
    simpa only [sub_zero] using differentiable_detPower_parameter q.out hs 0
  exact (((hWd _).mul (hVd _)).mul_const _).mul hP.differentiableOn

end Langlands.Global.RankinSelbergGlobal.ComplexJacquet
