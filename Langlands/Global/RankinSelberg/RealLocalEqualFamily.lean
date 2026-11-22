import Langlands.Global.RankinSelberg.RealEqualConvergence
import Langlands.Global.RankinSelberg.RealUnequalFamilyGauge
import Langlands.Global.RankinSelberg.ComplexUnequalOrdinaryFamily

/-! # Holomorphy of real equal-rank integrals in Whittaker families -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

open Langlands.Archimedean (unitaryCompact)
open Langlands.RankinSelberg (LeftUnipotentQuotient lastRow)
open Langlands.QuotientIntegration (descend)
open ArchimedeanLocal RealIwasawa RealConvergenceAnalysis RealEqualConvergence
open RealUnequalFamily (HasLeftCharacter HasUniformGauge)
open ComplexUnequalFamily (HalfPlaneDomination differentiableOn_integral_of_halfPlaneDomination)

private local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear (n + 1) ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear (n + 1) ℝ) := ⟨rfl⟩
private local instance (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear.upperUnipotent (n + 1) ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear.upperUnipotent (n + 1) ℝ) :=
  ⟨rfl⟩
private local instance (n : ℕ) : MeasurableSpace (LeftUnipotentQuotient n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (LeftUnipotentQuotient n ℝ) := ⟨rfl⟩

variable {r : ℕ}

local notation "G" => Langlands.GeneralLinear (r + 1) ℝ
local notation "Q" => LeftUnipotentQuotient r ℝ
local notation "Row" => Fin (r + 1) → ℝ

/-- The exact toral marginal of a real quotient measure integrates the majorant
`exp(-∑ |y_j| - L y)` after its density `exp(L y)` cancels. -/
theorem integrable_realToralMajorant (ν : Measure Q) (κ : ℝ≥0) (L : Row →L[ℝ] ℝ)
    (hκL : ∀ B : Row → ℝ≥0∞, Measurable B →
      ∫⁻ q, B (alphaQ q) ∂ν = (κ : ℝ≥0∞) * ∫⁻ y, ENNReal.ofReal (Real.exp (L y)) * B y) :
    Integrable (fun q => Real.exp (-(∑ j, |alphaQ q j|) - L (alphaQ q))) ν := by
  let B := fun y : Row => Real.exp (-(∑ j, |y j|) - L y)
  have hBc : Continuous B := Real.continuous_exp.comp
    ((continuous_finsetSum _ fun j _ => (continuous_apply j).abs).neg.sub L.continuous)
  refine ⟨(hBc.comp continuous_alphaQ).aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun q => Real.exp_nonneg _)).2 ?_⟩
  change (∫⁻ q, ENNReal.ofReal (B (alphaQ q)) ∂ν) < ⊤
  have hscale (y : Row) :
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

private theorem family_invariant {a : ℝˣ} {W V : G → ℂ}
    (hW : HasLeftCharacter a W) (hV : HasLeftCharacter (-a) V) :
    ∀ u ∈ Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ, ∀ g,
      W (u * g) * V (u * g) = W g * V g := by
  intro u hu g
  rw [hW u hu g, hV u hu g]
  calc
    _ = (realWhittakerCharacter a u * realWhittakerCharacter (-a) u) * (W g * V g) := by ring
    _ = _ := by rw [realWhittakerCharacter_mul_neg, one_mul]

private theorem continuous_family_kernel {a : ℝˣ} {W V : G → ℂ}
    (hW : HasLeftCharacter a W) (hV : HasLeftCharacter (-a) V)
    (hWc : Continuous W) (hVc : Continuous V) (Φ : Row → ℂ) (hΦ : Continuous Φ) :
    Continuous (fun q : Q => kernel W V Φ q.out) := by
  have hkinv : ∀ h : Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ, ∀ g,
      kernel W V Φ (h.val * g) = kernel W V Φ g :=
    fun h g => kernel_unipotent_mul (family_invariant hW hV) h g
  have hfe : (fun q : Q => kernel W V Φ q.out) =
      descend (Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ) (kernel W V Φ) hkinv :=
    funext fun q => out_eq_descend _ hkinv q
  rw [hfe]
  exact continuous_descend hkinv (continuous_kernel hWc hVc hΦ)

private theorem continuous_quotient_logDet : Continuous (fun q : Q => logDet q.out) := by
  have hlinv : ∀ h : Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ, ∀ g,
      logDet (h.val * g) = logDet g := fun h g => logDet_unipotent_mul h g
  have hℓe : (fun q : Q => logDet q.out) =
      descend (Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ) logDet hlinv :=
    funext fun q => out_eq_descend _ hlinv q
  rw [hℓe]
  exact continuous_descend_real hlinv continuous_logDet

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

variable (r E) in
/-- On a common spectral right half-plane, uniform gauge estimates for two real Whittaker
families with opposite characters imply integrability and joint holomorphy of the real
equal-rank integral in the family parameter. -/
def RealLocalEqualFamilyStatement : Prop :=
  ∀ (a : ℝˣ) (D : RealQuotientMeasureData r) (S : Set E) (W V : E → G → ℂ)
    (s : E → ℂ) (Φ : 𝓢(Row, ℂ)), IsOpen S → Differentiable ℂ s →
    (∀ p, HasLeftCharacter a (W p)) → (∀ p, HasLeftCharacter (-a) (V p)) →
    (∀ p, Continuous (W p)) → (∀ p, Continuous (V p)) →
    (∀ g, DifferentiableOn ℂ (W · g) S) → (∀ g, DifferentiableOn ℂ (V · g) S) →
    HasUniformGauge S W → HasUniformGauge S V →
    ∃ σ : ℝ,
      (∀ p ∈ S ∩ {v | σ < (s v).re},
        Integrable (realEqualIntegrand (W p) (V p) Φ (s p)) D.measure) ∧
      DifferentiableOn ℂ (fun p => realEqualIntegral D (W p) (V p) Φ (s p))
        (S ∩ {v | σ < (s v).re})

set_option maxHeartbeats 800000 in
theorem realLocalEqualFamily : RealLocalEqualFamilyStatement r E := by
  intro a D S W V s Φ hS hs hW hV hWc hVc hWd hVd hWb hVb
  have := D.groupHaar_isHaar
  have := D.unipotentHaar_isHaar
  have := D.unipotentHaar_rightInvariant
  obtain ⟨κ, L, hκL⟩ :=
    exists_lintegral_alphaQ D.groupHaar D.unipotentHaar D.measure D.compatible
  obtain ⟨N1, hN1⟩ := hWb
  obtain ⟨N2, hN2⟩ := hVb
  obtain ⟨C2, hC2, hb2⟩ := hN2 0
  let A : ℝ := (N1 : ℝ) + N2 + ‖L‖
  have hA : 0 ≤ A := by positivity
  let σ : ℝ := (A + 1) * ((r : ℝ) + 1)
  have hF (p : E) : realEqualIntegrand (W p) (V p) Φ (s p) =
      fun q => kernel (W p) (V p) Φ q.out * Complex.exp (s p * (logDet q.out : ℂ)) :=
    realEqualIntegrand_eq _ _ _ _
  have hdom : HalfPlaneDomination D.measure S s
      (fun p => realEqualIntegrand (W p) (V p) Φ (s p)) σ := by
    intro τ
    let M : ℕ := ⌈(A + 1) * ((r : ℝ) + 1) + τ * ((r : ℝ) + 1)⌉₊
    obtain ⟨C1, hC1, hb1⟩ := hN1 M
    obtain ⟨C3, hC3, hb3⟩ := exists_norm_le_exp (hasRapidDecay_schwartz Φ)
      (c := (r : ℝ) + 1) (by positivity) M
    refine ⟨fun q => C1 * C2 * C3 * Real.exp (-(∑ j, |alphaQ q j|) - L (alphaQ q)),
      (integrable_realToralMajorant D.measure κ L hκL).const_mul _,
      fun p hp hpσ hpτ q => ?_⟩
    have hkinv : ∀ h : Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ, ∀ g,
        kernel (W p) (V p) Φ (h.val * g) = kernel (W p) (V p) Φ g :=
      fun h g => kernel_unipotent_mul (family_invariant (hW p) (hV p)) h g
    have hlinv : ∀ h : Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ, ∀ g,
        logDet (h.val * g) = logDet g := fun h g => logDet_unipotent_mul h g
    set y := alphaQ q with hy
    set k := kpart q.out with hk
    set x := torus y * (k : Langlands.GeneralLinear (r + 1) ℝ) with hx
    have hfq : kernel (W p) (V p) Φ q.out = kernel (W p) (V p) Φ x := by
      rw [hx, hy, hk, ← alpha_out q]
      exact eq_torus_mul_kpart (kernel (W p) (V p) Φ) hkinv q.out
    have hℓq : logDet q.out = ∑ j, y j := by
      rw [hy, ← alpha_out q, ← logDet_torus_mul (alpha q.out) (kpart q.out)]
      exact eq_torus_mul_kpart logDet hlinv q.out
    have hW1 := hb1 p hp y k
    have hW2 := hb2 p hp y k
    have hΦ3 := hb3 (Langlands.RankinSelberg.lastRow x) (y (Fin.last r)) (exp_le_mul_norm_lastRow y k)
    have hker : ‖kernel (W p) (V p) Φ x‖ ≤
        (C1 * Real.exp (-(M : ℝ) * rootPos y + (N1 : ℝ) * ∑ j, |y j|)) *
          (C2 * Real.exp (-((0 : ℕ) : ℝ) * rootPos y + (N2 : ℝ) * ∑ j, |y j|)) *
          (C3 * Real.exp (-(M : ℝ) * max (y (Fin.last r)) 0)) := by
      unfold kernel
      rw [norm_mul, norm_mul]
      exact mul_le_mul (mul_le_mul hW1 hW2 (norm_nonneg _) (by positivity)) hΦ3
        (norm_nonneg _) (by positivity)
    have ht : (A + 1) * ((r : ℝ) + 1) ≤ (s p).re := hpσ.le
    have hM : (A + 1) * ((r : ℝ) + 1) + (s p).re * ((r : ℝ) + 1) ≤ (M : ℝ) := by
      refine le_trans ?_ (Nat.le_ceil _)
      have := mul_le_mul_of_nonneg_right hpτ (show (0 : ℝ) ≤ (r : ℝ) + 1 by positivity)
      linarith
    have hexpo := exponent_le y (A := A) (t := (s p).re) (M := (M : ℝ)) (K := (M : ℝ)) hA ht hM hM
    have hlin := linear_le L y
    have hsum : 0 ≤ ∑ j, |y j| := Finset.sum_nonneg fun j _ => abs_nonneg _
    have hfinal : -(M : ℝ) * rootPos y + ((N1 : ℝ) + N2) * ∑ j, |y j| + (s p).re * ∑ j, y j -
        (M : ℝ) * max (y (Fin.last r)) 0 ≤ -(∑ j, |y j|) - L y := by
      have hL0 : 0 ≤ ‖L‖ * ∑ j, |y j| := mul_nonneg (norm_nonneg _) hsum
      dsimp only [A] at hexpo
      nlinarith
    show ‖realEqualIntegrand (W p) (V p) Φ (s p) q‖ ≤
      C1 * C2 * C3 * Real.exp (-(∑ j, |y j|) - L y)
    rw [hF p]
    change ‖kernel (W p) (V p) Φ q.out * Complex.exp (s p * (logDet q.out : ℂ))‖ ≤ _
    rw [norm_mul, norm_cexp_mul_ofReal, hfq, hℓq]
    calc
      ‖kernel (W p) (V p) Φ x‖ * Real.exp ((s p).re * ∑ j, y j) ≤
          ((C1 * Real.exp (-(M : ℝ) * rootPos y + (N1 : ℝ) * ∑ j, |y j|)) *
            (C2 * Real.exp (-((0 : ℕ) : ℝ) * rootPos y + (N2 : ℝ) * ∑ j, |y j|)) *
            (C3 * Real.exp (-(M : ℝ) * max (y (Fin.last r)) 0))) *
            Real.exp ((s p).re * ∑ j, y j) :=
        mul_le_mul_of_nonneg_right hker (Real.exp_pos _).le
      _ = C1 * C2 * C3 * Real.exp (-(M : ℝ) * rootPos y + ((N1 : ℝ) + N2) * ∑ j, |y j| +
            (s p).re * ∑ j, y j - (M : ℝ) * max (y (Fin.last r)) 0) := by
        rw [show -(M : ℝ) * rootPos y + ((N1 : ℝ) + N2) * ∑ j, |y j| +
              (s p).re * ∑ j, y j - (M : ℝ) * max (y (Fin.last r)) 0 =
            (-(M : ℝ) * rootPos y + (N1 : ℝ) * ∑ j, |y j|) +
              (-((0 : ℕ) : ℝ) * rootPos y + (N2 : ℝ) * ∑ j, |y j|) +
              (-(M : ℝ) * max (y (Fin.last r)) 0) + (s p).re * ∑ j, y j by push_cast; ring]
        simp only [Real.exp_add]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hfinal) (by positivity)
  refine ⟨σ, differentiableOn_integral_of_halfPlaneDomination hS hs (fun p => ?_)
    (fun q => ?_) hdom⟩
  · rw [hF p]
    exact ((continuous_family_kernel (hW p) (hV p) (hWc p) (hVc p) Φ Φ.continuous).mul
      (Complex.continuous_exp.comp (continuous_const.mul
        (Complex.continuous_ofReal.comp continuous_quotient_logDet)))).aestronglyMeasurable
  · change DifferentiableOn ℂ (fun p => realEqualIntegrand (W p) (V p) Φ (s p) q) S
    simp only [hF]
    unfold kernel
    have hexp : Differentiable ℂ (fun p => Complex.exp (s p * (logDet q.out : ℂ))) :=
      Complex.differentiable_exp.comp (hs.mul_const _)
    exact (((hWd _).mul (hVd _)).mul_const _).mul hexp.differentiableOn

end Langlands.Global.RankinSelbergGlobal.RealGodement
