import Langlands.Global.RankinSelberg.ComplexUnequalOrdinaryFamily
import Langlands.Global.RankinSelberg.RealUnequalFamilyGauge

/-! # Joint holomorphy of the real ordinary unequal-rank integral over a parameter family -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.RealUnequalFamily

open Langlands.Archimedean (unitaryCompact)
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open Langlands.QuotientIntegration (descend leftQuotient_isOpenQuotientMap leftQuotientMap_apply)
open ArchimedeanLocal RealIwasawa RealConvergenceAnalysis RealEqualConvergence
open ComplexUnequalFamily (HalfPlaneDomination differentiableOn_integral_of_halfPlaneDomination)

attribute [local instance] archimedeanRealGLMeasurable archimedeanRealGLBorel
  archimedeanRealNMeasurable archimedeanRealNBorel archimedeanRealQMeasurable
  archimedeanRealQBorel

variable {r t : ℕ} (h : t < r) {a : ℝˣ}
local notation "GT" => Langlands.GeneralLinear (t + 1) ℝ
local notation "GR" => Langlands.GeneralLinear (r + 1) ℝ

/-- The padded product of functions with opposite left characters is left invariant under the
upper unipotent group of the smaller group. -/
theorem product_unipotent_mul {W : GR → ℂ} {V : GT → ℂ}
    (hW : HasLeftCharacter a W) (hV : HasLeftCharacter (-a) V)
    (u : Langlands.GeneralLinear.upperUnipotent (t + 1) ℝ) (g : GT) :
    W (padGL (Nat.le_of_lt (Nat.succ_lt_succ h)) (u.val * g)) * V (u.val * g) =
      W (padGL (Nat.le_of_lt (Nat.succ_lt_succ h)) g) * V g := by
  set hp : t + 1 ≤ r + 1 := Nat.le_of_lt (Nat.succ_lt_succ h)
  rw [map_mul, hW _ (RealUnequalConvergence.padGL_mem_upperUnipotent hp u.2) _, hV u.val u.2 g,
    RealUnequalConvergence.realWhittakerCharacter_padGL h hp]
  calc
    realWhittakerCharacter a u.val * W (padGL hp g) * (realWhittakerCharacter (-a) u.val * V g) =
        (realWhittakerCharacter a u.val * realWhittakerCharacter (-a) u.val) *
          (W (padGL hp g) * V g) := by ring
    _ = W (padGL hp g) * V g := by rw [realWhittakerCharacter_mul_neg, one_mul]

/-- The real ordinary integrand evaluated at the class of any representative. -/
theorem integrand_mk {W : GR → ℂ} {V : GT → ℂ}
    (hW : HasLeftCharacter a W) (hV : HasLeftCharacter (-a) V) (s : ℂ) (g : GT) :
    realUnequalIntegrand h W V s (Quotient.mk _ g) =
      W (padGL (Nat.le_of_lt (Nat.succ_lt_succ h)) g) * V g *
        Complex.exp ((s - ((r - t : ℕ) : ℂ) / 2) * (logDet g : ℂ)) := by
  let f : GT → ℂ := fun g => W (padGL (Nat.le_of_lt (Nat.succ_lt_succ h)) g) * V g *
    Complex.exp ((s - ((r - t : ℕ) : ℂ) / 2) * (logDet g : ℂ))
  have hf : ∀ u : Langlands.GeneralLinear.upperUnipotent (t + 1) ℝ, ∀ g, f (u.val * g) = f g := by
    intro u g
    simp only [f]
    rw [product_unipotent_mul h hW hV, logDet_unipotent_mul]
  exact congrArg (descend _ f hf) (Quotient.out_eq (Quotient.mk _ g))

/-- The real ordinary integrand is continuous on the left quotient. -/
theorem continuous_integrand {W : GR → ℂ} {V : GT → ℂ}
    (hW : HasLeftCharacter a W) (hV : HasLeftCharacter (-a) V)
    (hWc : Continuous W) (hVc : Continuous V) (s : ℂ) :
    Continuous (realUnequalIntegrand h W V s) := by
  apply (leftQuotient_isOpenQuotientMap
    (Langlands.GeneralLinear.upperUnipotent (t + 1) ℝ)).isQuotientMap.continuous_iff.mpr
  simp only [Function.comp_def, leftQuotientMap_apply, integrand_mk h hW hV]
  exact ((hWc.comp (UnequalAnalytic.continuous_padGL _)).mul hVc).mul
    (Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp continuous_logDet)))

theorem continuous_exp_neg_sum_abs_sub (L : (Fin (t + 1) → ℝ) →L[ℝ] ℝ) :
    Continuous (fun y : Fin (t + 1) → ℝ => -(∑ j, |y j|) - L y) :=
  (continuous_finsetSum _ fun j _ => (continuous_apply j).abs).neg.sub L.continuous

/-- Uniform gauge estimates give common integrable majorants for the real ordinary kernel on
bounded intervals of the real part of the spectral variable above a fixed threshold. -/
theorem ordinary_halfPlaneDomination {P : Type*} (D : RealQuotientMeasureData t)
    (S : Set P) (W : P → GR → ℂ) (V : P → GT → ℂ) (s : P → ℂ)
    (hW : ∀ p, HasLeftCharacter a (W p)) (hV : ∀ p, HasLeftCharacter (-a) (V p))
    (hWb : HasUniformGauge S W) (hVb : HasUniformGauge S V) :
    ∃ σ, HalfPlaneDomination D.measure S s
      (fun p => realUnequalIntegrand h (W p) (V p) (s p)) σ := by
  have := D.groupHaar_isHaar
  have := D.unipotentHaar_isHaar
  have := D.unipotentHaar_rightInvariant
  obtain ⟨κ, L, hκL⟩ :=
    exists_lintegral_alphaQ D.groupHaar D.unipotentHaar D.measure D.compatible
  set hp : t + 1 ≤ r + 1 := Nat.le_of_lt (Nat.succ_lt_succ h) with hhp
  obtain ⟨N1, hN1⟩ := hWb.pad h hp
  obtain ⟨N2, hN2⟩ := hVb
  obtain ⟨C2, hC2, hb2⟩ := hN2 0
  set A : ℝ := (N1 : ℝ) + N2 + ‖L‖ with hA
  set c : ℝ := ((r - t : ℕ) : ℝ) / 2 with hc
  have hA0 : 0 ≤ A := by positivity
  have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  refine ⟨(A + 1) * ((t : ℝ) + 1) + c, fun τ => ?_⟩
  set M : ℕ := ⌈(A + 1) * ((t : ℝ) + 1) + (τ - c) * ((t : ℝ) + 1)⌉₊ with hM
  obtain ⟨C1, hC1, hb1⟩ := hN1 M
  refine ⟨fun q => C1 * C2 * Real.exp (-(∑ j, |alphaQ q j|) - L (alphaQ q)),
    (RealUnequalDualConvergence.integrable_exp_comp_alphaQ hκL
      (continuous_exp_neg_sum_abs_sub L) (fun y => by linarith)).const_mul _,
    fun v hv hvσ hvτ q => ?_⟩
  set T : ℝ := (s v).re - c with hT
  have hT0 : (A + 1) * ((t : ℝ) + 1) ≤ T := by linarith
  have hTM : (A + 1) * ((t : ℝ) + 1) + T * ((t : ℝ) + 1) ≤ M := by
    refine le_trans ?_ (Nat.le_ceil _)
    have hTτ : T ≤ τ - c := by linarith
    nlinarith
  have hrep : ∀ (y : Fin (t + 1) → ℝ) (k : unitaryCompact ℝ (t + 1)),
      ‖realUnequalIntegrand h (W v) (V v) (s v)
          (Quotient.mk _ (torus y * (k : GT)))‖ ≤
        C1 * C2 * Real.exp (-(∑ j, |y j|) - L y) := by
    intro y k
    rw [integrand_mk h (hW v) (hV v), norm_mul, norm_mul, logDet_torus_mul,
      norm_cexp_mul_ofReal]
    have hre : (s v - ((r - t : ℕ) : ℂ) / 2).re = T := by
      rw [hT, hc, Complex.sub_re, Complex.div_re]
      simp
      ring
    rw [hre]
    have h1 := hb1 v hv y k
    have h2 := hb2 v hv y k
    have hE := exponent_le y (A := A) (t := T) (M := (M : ℝ)) (K := (M : ℝ)) hA0 hT0 hTM hTM
    have hLy := linear_le L y
    have hS : 0 ≤ ∑ j, |y j| := Finset.sum_nonneg fun j _ => abs_nonneg _
    calc
      _ ≤ (C1 * Real.exp (-(M : ℝ) * rootPos y + (N1 : ℝ) * ∑ j, |y j| -
            (M : ℝ) * max (y (Fin.last t)) 0)) *
          (C2 * Real.exp (-((0 : ℕ) : ℝ) * rootPos y + (N2 : ℝ) * ∑ j, |y j|)) *
          Real.exp (T * ∑ j, y j) :=
        mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 (norm_nonneg _) (by positivity))
          (Real.exp_nonneg _)
      _ = C1 * C2 * Real.exp (-(M : ℝ) * rootPos y + ((N1 : ℝ) + N2) * ∑ j, |y j| +
            T * ∑ j, y j - (M : ℝ) * max (y (Fin.last t)) 0) := by
        rw [mul_mul_mul_comm, mul_assoc, ← Real.exp_add, ← Real.exp_add]
        congr 2
        push_cast
        ring
      _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (mul_nonneg hC1 hC2)
        rw [hA] at hE
        nlinarith
  induction q using Quotient.inductionOn with
  | h g =>
    dsimp only
    rw [alphaQ_mk, mk_eq_mk_torus_mul_kpart g]
    exact hrep (alpha g) (kpart g)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- Holomorphy and integrability of the real ordinary unequal-rank integral, jointly in a
finite-dimensional complex parameter space, for families with uniform gauge estimates. -/
def RealUnequalOrdinaryFamilyStatement : Prop :=
  ∀ (D : RealQuotientMeasureData t) (S : Set E) (W : E → GR → ℂ) (V : E → GT → ℂ)
    (s : E → ℂ), IsOpen S → Differentiable ℂ s →
    (∀ p, HasLeftCharacter a (W p)) → (∀ p, HasLeftCharacter (-a) (V p)) →
    (∀ p, Continuous (W p)) → (∀ p, Continuous (V p)) →
    (∀ g, DifferentiableOn ℂ (W · g) S) → (∀ g, DifferentiableOn ℂ (V · g) S) →
    HasUniformGauge S W → HasUniformGauge S V →
    ∃ σ : ℝ,
      (∀ p ∈ S ∩ {v | σ < (s v).re},
        Integrable (realUnequalIntegrand h (W p) (V p) (s p)) D.measure) ∧
      DifferentiableOn ℂ (fun p => realUnequalIntegral h D (W p) (V p) (s p))
        (S ∩ {v | σ < (s v).re})

theorem realUnequalOrdinaryFamily :
    RealUnequalOrdinaryFamilyStatement (E := E) (a := a) h := by
  intro D S W V s hS hs hW hV hWc hVc hWd hVd hWb hVb
  obtain ⟨σ, hdom⟩ := ordinary_halfPlaneDomination h D S W V s hW hV hWb hVb
  refine ⟨σ, differentiableOn_integral_of_halfPlaneDomination hS hs (fun p =>
    (continuous_integrand h (hW p) (hV p) (hWc p) (hVc p) (s p)).aestronglyMeasurable)
      (fun q => ?_) hdom⟩
  change DifferentiableOn ℂ (fun p =>
    W p (padGL (Nat.le_of_lt (Nat.succ_lt_succ h)) q.out) * V p q.out *
      Complex.exp ((s p - ((r - t : ℕ) : ℂ) / 2) * (logDet q.out : ℂ))) S
  exact ((hWd _).mul (hVd _)).mul
    (Complex.differentiable_exp.comp ((hs.sub_const _).mul_const _)).differentiableOn

end Langlands.Global.RankinSelbergGlobal.RealUnequalFamily
