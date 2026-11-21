import Langlands.Global.RankinSelberg.ComplexLastRowSchwartz
import Langlands.Global.RankinSelberg.ComplexLocalEqualMeromorphicReduction
import Langlands.Global.RankinSelberg.ComplexUnequalOrdinaryFamily

/-! # Uniform control in the Schwartz test on an equal-rank spectral line -/

noncomputable section

open MeasureTheory
open Langlands.Archimedean Langlands.LocalFactor.Archimedean
open scoped SchwartzMap NNReal Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquet

open ArchimedeanLocal ComplexLocalIwasawa ComplexLocalConvergence
open ComplexCharacterChange (complexEqualIntegrand_mk model_pair_invariant)
open ComplexLocalWhittakerGauge (logTorus logTorus_val)
open ComplexLocalOrdinaryConvergence (norm_detPower_logTorus_mul)
open ComplexUnequalFamily (sum_add_abs integrable_toralMajorant)
open ComplexLastRowSchwartz
open Langlands.RankinSelberg (LeftUnipotentQuotient lastRow)

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

variable {r : ℕ}

local notation "I" => Fin (r + 1)
local notation "G" => Langlands.GeneralLinear (r + 1) ℂ
local notation "K" => unitaryCompact ℂ (r + 1)
local notation "Q" => LeftUnipotentQuotient r ℂ
local notation "Test" => 𝓢(I → ℂ, ℂ)

private theorem sum_abs_split (y : I → ℝ) :
    (∑ j, |y j|) = positiveLogSum y + positiveLogSum (-y) := by
  unfold positiveLogSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  change |y j| = max (y j) 0 + max (-y j) 0
  rcases le_total 0 (y j) with hj | hj
  · rw [abs_of_nonneg hj, max_eq_left hj, max_eq_right (neg_nonpos.mpr hj), add_zero]
  · rw [abs_of_nonpos hj, max_eq_right hj, max_eq_left (neg_nonneg.mpr hj), zero_add]

private theorem positiveLog_le_root_last (y : I → ℝ) :
    positiveLogSum y ≤ (r + 1) * (max (y (Fin.last r)) 0 + simpleRootLogSum y) := by
  have h0 : 0 ≤ simpleRootLogSum y := Finset.sum_nonneg fun _ _ => le_max_right _ _
  unfold positiveLogSum
  calc
    _ ≤ ∑ _j : I, (max (y (Fin.last r)) 0 + simpleRootLogSum y) := by
      refine Finset.sum_le_sum fun j _ => max_le ?_ (add_nonneg (le_max_right _ _) h0)
      exact (coord_le_last_add_simpleRootLogSum r y j).trans (add_le_add (le_max_left _ _) le_rfl)
    _ = _ := by simp [nsmul_eq_mul, mul_add]

/-- A common half-plane works for every last-row Schwartz test. On each vertical
line in that half-plane the integral is bounded by a continuous test seminorm. -/
def ComplexLocalEqualTraceBoundStatement : Prop :=
  ∀ (ds es : List ComplexCharacterData), ds.length = r + 1 → es.length = r + 1 →
  ∀ (a : ℂˣ) (D : ComplexQuotientMeasureData r) (W V : G → ℂ),
    W ∈ complexWhittakerModel r ds a → V ∈ complexWhittakerModel r es (-a) →
    ∃ σ : ℝ, ∀ t : ℝ, σ < t → ∃ p : Test → ℝ, Continuous p ∧ p 0 = 0 ∧
      ∀ (Φ : Test) (s : ℂ), s.re = t →
        Integrable (complexEqualIntegrand W V Φ s) D.measure ∧
        ‖complexEqualIntegral D W V Φ s‖ ≤ p Φ

theorem complexLocalEqualTraceBound : ComplexLocalEqualTraceBoundStatement (r := r) := by
  intro ds es hds hes a D W V hW hV
  have hB := complexLocalWhittakerSimpleRootBound_of_uniformGrowth complexLocalWhittakerUniformGrowth
  obtain ⟨A, hA, hWB⟩ := hB r ds hds a W hW
  obtain ⟨A', hA', hVB⟩ := hB r es hes (-a) V hV
  obtain ⟨κ, L, hκL⟩ := complexIwasawaToralMeasure r D
  let σ := (A + A' + ‖L‖ + 1) / 2
  let B (q : Q) := Real.exp (-(∑ j, |alphaQ q j|) - L (alphaQ q))
  have hBint : Integrable B D.measure := integrable_toralMajorant D κ L hκL
  refine ⟨σ, fun t ht => ?_⟩
  have ht' : A + A' + ‖L‖ + 1 ≤ 2 * t := by dsimp [σ] at ht; linarith
  have ht₀ : 0 ≤ t := by linarith [norm_nonneg L]
  obtain ⟨m, hm⟩ := exists_nat_gt (2 * (2 * t) * (r + 1))
  obtain ⟨C, hC, hWm⟩ := hWB m (Nat.cast_nonneg _)
  obtain ⟨C', hC', hV0⟩ := hVB 0 le_rfl
  let p (Φ : Test) := C * C' * lastRowTestBound m Φ
  have hp : Continuous p := (continuous_lastRowTestBound m).const_mul _
  let F (Φ : Test) := p Φ * ∫ q, B q ∂D.measure
  refine ⟨F, hp.mul_const _, by simp [F, p], fun Φ s hs => ?_⟩
  have hmajor (q : Q) : ‖complexEqualIntegrand W V Φ s q‖ ≤ p Φ * B q := by
    induction q using Quotient.inductionOn with
    | h g =>
      dsimp only [B]
      rw [alphaQ_mk, mk_eq_mk_logTorus_mul_kpart g,
        complexEqualIntegrand_mk (model_pair_invariant hW hV)]
      let y := alpha g
      let k := kpart g
      let S := ∑ j, |y j|
      let R := simpleRootLogSum y
      let u := max (y (Fin.last r)) 0
      have hdiag : expDiagonal y = logTorus y :=
        Units.ext (by rw [expDiagonal_val, logTorus_val])
      have h1 := hWm y k
      have h2 := hV0 y k
      rw [hdiag, ← sum_abs_split] at h1 h2
      simp only [zero_mul, sub_zero] at h2
      have h3 := norm_lastRow_le_testBound Φ m y k
      have hP := mul_le_mul_of_nonneg_left (positiveLog_le_root_last y) (show 0 ≤ 2 * (2 * t) by positivity)
      have hR : 0 ≤ u + R := add_nonneg (le_max_right _ _)
        (Finset.sum_nonneg fun _ _ => le_max_right _ _)
      have hM := mul_le_mul_of_nonneg_right hm.le hR
      have hexp :
          (A + A') * S - (m : ℝ) * (u + R) + 2 * t * (∑ j, y j) ≤ -S - L y := by
        have hsum := congrArg ((2 * t) * ·) (sum_add_abs y)
        have hS : 0 ≤ S := Finset.sum_nonneg fun j _ => abs_nonneg _
        have hT := mul_le_mul_of_nonneg_right ht' hS
        dsimp only [S, R, u, positiveLogSum] at hP hM hsum hT ⊢
        linarith [RealEqualConvergence.linear_le L y]
      rw [norm_mul, norm_mul, norm_mul, norm_detPower_logTorus_mul, hs]
      calc
        _ ≤ (C * Real.exp (A * S - (m : ℝ) * R)) * (C' * Real.exp (A' * S)) *
            (lastRowTestBound m Φ * Real.exp (-(m : ℝ) * u)) *
              Real.exp (2 * t * ∑ j, y j) := by
          gcongr
        _ = p Φ * Real.exp ((A + A') * S - (m : ℝ) * (u + R) + 2 * t * ∑ j, y j) := by
          have he : (A + A') * S - (m : ℝ) * (u + R) + 2 * t * ∑ j, y j =
              (A * S - (m : ℝ) * R) + A' * S + (-(m : ℝ) * u) + 2 * t * ∑ j, y j := by ring
          rw [he, Real.exp_add, Real.exp_add, Real.exp_add]
          dsimp only [p]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp)
          (mul_nonneg (mul_nonneg hC hC') (lastRowTestBound_nonneg m Φ))
  have hmeas : AEStronglyMeasurable (complexEqualIntegrand W V Φ s) D.measure := by
    have hQ := Langlands.QuotientIntegration.leftQuotient_isOpenQuotientMap
      (GeneralLinear.upperUnipotent (r + 1) ℂ)
    apply Continuous.aestronglyMeasurable
    apply hQ.isQuotientMap.continuous_iff.mpr
    have hWc := (contMDiff_of_mem_complexWhittakerModel hW).continuous
    have hVc := (contMDiff_of_mem_complexWhittakerModel hV).continuous
    have hrow : Continuous (Langlands.RankinSelberg.lastRow : G → I → ℂ) :=
      continuous_pi fun j => (GeneralLinear.entry (Fin.last r) j).continuous
    have hdet : Continuous (fun g : G => complexNormalizedAbs g.val.det) :=
      Units.continuous_val.matrix_det.norm.pow 2
    have hd : Continuous (fun g : G => ArchimedeanLocal.detPower complexNormalizedAbs g s) :=
      Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
        (hdet.log fun g => pow_ne_zero 2 (norm_ne_zero_iff.mpr g.det_ne_zero))))
    change Continuous (fun g : G => complexEqualIntegrand W V Φ s (Quotient.mk _ g))
    simp only [complexEqualIntegrand_mk (model_pair_invariant hW hV)]
    exact ((hWc.mul hVc).mul (Φ.continuous.comp hrow)).mul hd
  have hBint' := hBint.const_mul (p Φ)
  exact ⟨hBint'.mono' hmeas (.of_forall hmajor), by
    exact (norm_integral_le_of_norm_le hBint' (.of_forall hmajor)).trans_eq
      (integral_const_mul (p Φ) B)⟩

end Langlands.Global.RankinSelbergGlobal.ComplexJacquet
