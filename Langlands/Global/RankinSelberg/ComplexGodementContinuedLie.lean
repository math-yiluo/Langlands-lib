import Langlands.Global.RankinSelberg.ComplexGodementStandardLie

/-! # The same Lie derivative formula for continued Godement values -/

noncomputable section
open MeasureTheory Set
open scoped Classical ContDiff Manifold Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodement

open Langlands.Archimedean (matrixModel rightDerivative characterOfParams)
open Langlands.GeneralLinear (determinant)
open Langlands.HarmonicAnalysis (AdditiveHaarMeasure)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData)
open Langlands.Analysis.SchwartzMatrixNorm (EntrySchwartz)
open ComplexGodementAddedCharacter (rightTest continuedValue)
open ComplexGodementParametric (directionalTest hasDerivAt_integral_iteratedKernel_curve)
open ComplexGodementContinuedSmooth (testDerivative translatedIntegral contMDiff_continuedValue)
open ComplexGodementWhittakerFamily (HasUniformSimpleRootBound)
open ArchimedeanLocal (complexNormalizedAbs)

attribute [local instance] ArchimedeanLocal.archimedeanComplexGLMeasurable
  ArchimedeanLocal.archimedeanComplexGLBorel

variable {r : ℕ}
local notation "G" => Langlands.GeneralLinear (r + 1) ℂ
local notation "G'" => Langlands.GeneralLinear (r + 1 + 1) ℂ
local notation "Square" => Matrix (Fin (r + 1 + 1)) (Fin (r + 1 + 1)) ℂ
local notation "Rect" => Matrix (Fin (r + 1)) (Fin (r + 1 + 1)) ℂ
local notation "Test" => EntrySchwartz (r + 1) (r + 1 + 1)

private theorem shifted_character_apply (d : ComplexCharacterData) (s : ℂ) (z : ℂˣ) :
    ((characterOfParams d.weight (d.exponent + s)).character z : ℂ) =
      (d.character z : ℂ) * normPower s z := by
  have hz : 0 < ‖(z : ℂ)‖ := norm_pos_iff.mpr z.ne_zero
  have hne : (‖(z : ℂ)‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz.ne'
  have hnorm : normPower s z = (‖(z : ℂ)‖ : ℂ) ^ (2 * s) := by
    change ((‖(z : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ s = _
    rw [pow_two, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hz.le hz.le,
      ← Complex.cpow_add _ _ hne]
    congr 1
    ring
  rw [(characterOfParams d.weight (d.exponent + s)).character_eq, d.character_eq, hnorm]
  change ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) ^ d.weight *
    (‖(z : ℂ)‖ : ℂ) ^ (2 * (d.exponent + s)) = _
  rw [mul_add, Complex.cpow_add _ _ hne, mul_assoc]

private theorem normPower_detPower {n : ℕ} (g : Langlands.GeneralLinear n ℂ) (s : ℂ) :
    normPower s (determinant g) = ArchimedeanLocal.detPower complexNormalizedAbs g s := by
  change ((complexNormalizedAbs g.val.det : ℝ) : ℂ) ^ s = _
  have hp : 0 < complexNormalizedAbs g.val.det := pow_pos (norm_pos_iff.mpr g.det_ne_zero) _
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hp.ne'), ← Complex.ofReal_log hp.le]
  simp only [ArchimedeanLocal.detPower, mul_comm _ s]

private theorem characterWeight_shifted (d : ComplexCharacterData) (s t : ℂ) (g : G') :
    characterWeight (characterOfParams d.weight (d.exponent + s)) t (determinant g) =
      characterWeight d t (determinant g) * ArchimedeanLocal.detPower complexNormalizedAbs g s := by
  change ((characterOfParams d.weight (d.exponent + s)).character (determinant g) : ℂ) *
    normPower t (determinant g) = (d.character (determinant g) : ℂ) * normPower t (determinant g) * _
  rw [shifted_character_apply, normPower_detPower]
  ring

private theorem continuedValue_eq_shiftedWeight (ν : Measure G) (μ : AdditiveHaarMeasure ℂ)
    (d : ComplexCharacterData) (a : ℂˣ) (Φ : Test) (W : G → ℂ) (g : G') (s : ℂ) :
    continuedValue ν μ d a Φ W g s =
      (d.character ((-1 : ℂˣ) ^ (r + 1)) : ℂ) *
        characterWeight (characterOfParams d.weight (d.exponent + s)) (((r + 1 : ℕ) : ℂ) / 2) (determinant g) *
        translatedIntegral ν μ a d W ((((r + 1 : ℕ) + 1 : ℂ) / 2) + s) Φ g := by
  rw [characterWeight_shifted, continuedValue, ← mul_assoc]
  rfl

open scoped Matrix.Norms.Elementwise in
private def rightField (X : Square) : Rect →L[ℝ] Rect :=
  (mulRightLinearMap (Fin (r + 1)) ℝ X).toContinuousLinearMap

open scoped Matrix.Norms.Elementwise in
set_option maxHeartbeats 750000 in
private theorem hasDerivAt_rectangular_rightExponential (g : G') (X : Square) (t : ℝ) (Y : Rect) :
    HasDerivAt (fun u => Y * (rightExponential g X u).val)
      (rightField X (Y * (rightExponential g X t).val)) t := by
  let : SeminormedAddCommGroup Square := Matrix.linftyOpSeminormedAddCommGroup
  let : NormedAddCommGroup Square := Matrix.linftyOpNormedAddCommGroup
  let : NormedSpace ℝ Square := Matrix.linftyOpNormedSpace
  let L : Square →L[ℝ] Rect := (mulLeftLinearMap (Fin (r + 1 + 1)) ℝ Y).toContinuousLinearMap
  have h := L.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_rightExponential_val g X t)
  change HasDerivAt (fun u => Y * (rightExponential g X u).val)
    (Y * ((rightExponential g X t).val * X)) t at h
  change HasDerivAt _ ((Y * (rightExponential g X t).val) * X) t
  rwa [Matrix.mul_assoc]

set_option maxHeartbeats 900000 in
/-- The continued value has the same determinant slope and the same right test derivative
as the standard section at the shifted inducing character. -/
theorem rightDerivative_continuedValue {P : Type} (ν : Measure G) [ν.IsHaarMeasure]
    (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ) (d : ComplexCharacterData) (S : Set P) (W : P → G → ℂ)
    (hWc : ∀ p ∈ S, Continuous (W p)) (hWb : HasUniformSimpleRootBound S W) (p : P) (hp : p ∈ S)
    (Φ : Test) (s : ℂ) (X : Square) :
    rightDerivative (matrixModel ℂ (r + 1 + 1)) X (fun g => continuedValue ν μ d a Φ (W p) g s) =
      determinantSlope (characterOfParams d.weight (d.exponent + s)) (((r + 1 : ℕ) : ℂ) / 2) X •
        (fun g => continuedValue ν μ d a Φ (W p) g s) +
        fun g => continuedValue ν μ d a (testDerivative Φ X) (W p) g s := by
  funext g
  let q : ℂ := (((r + 1 : ℕ) + 1 : ℂ) / 2) + s
  let C : ℂ := d.character ((-1 : ℂˣ) ^ (r + 1))
  let d' := characterOfParams d.weight (d.exponent + s)
  let γ := rightExponential g X
  have hs := hasDerivAt_rightDerivative_exponential
    (contMDiff_continuedValue ν μ a d W hWc hWb hp s Φ) g X
  have hI := hasDerivAt_integral_iteratedKernel_curve ν μ a d S W hWc hWb p hp Φ q γ
    (continuous_rightExponential g X) (rightField X)
    (fun t Y => hasDerivAt_rectangular_rightExponential g X t Y) 0
  have hTest : directionalTest (rightField X) Φ = testDerivative Φ X := rfl
  rw [hTest] at hI
  change HasDerivAt (fun t => translatedIntegral ν μ a d (W p) q Φ (γ t))
    (translatedIntegral ν μ a d (W p) q (testDerivative Φ X) (γ 0)) 0 at hI
  have hi : HasDerivAt (fun t => translatedIntegral ν μ a d (W p) q Φ (γ t))
      (translatedIntegral ν μ a d (W p) q (testDerivative Φ X) g) 0 := by
    simpa only [γ, rightExponential_zero] using hI
  have hc := (hasDerivAt_weight_rightExponential d' (((r + 1 : ℕ) : ℂ) / 2) g X).const_mul C
  have h := (hc.mul hi).deriv
  change deriv (fun t => C * characterWeight d' (((r + 1 : ℕ) : ℂ) / 2) (determinant (γ t)) *
      translatedIntegral ν μ a d (W p) q Φ (γ t)) 0 = _ at h
  rw [← hs.deriv]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, continuedValue_eq_shiftedWeight]
  change deriv (fun t => C * characterWeight d' (((r + 1 : ℕ) : ℂ) / 2) (determinant (γ t)) *
      translatedIntegral ν μ a d (W p) q Φ (γ t)) 0 = _
  rw [h]
  simp only [γ, rightExponential_zero]
  dsimp only [C, d', q]
  ring

variable (r) in
/-- Right differentiation of the partially transformed continued value has the determinant
slope at the shifted inducing character and differentiates the original Schwartz test. -/
def ComplexGodementContinuedLieStatement : Prop :=
  ∀ {P : Type} (ν : Measure G) [ν.IsHaarMeasure] (μ : AdditiveHaarMeasure ℂ)
    (a : ℂˣ) (d : ComplexCharacterData) (S : Set P) (W : P → G → ℂ),
    (∀ p ∈ S, Continuous (W p)) → HasUniformSimpleRootBound S W →
    ∀ p ∈ S, ∀ (Φ : Test) (s : ℂ) (X : Square),
      rightDerivative (matrixModel ℂ (r + 1 + 1)) X (fun g => continuedValue ν μ d a Φ (W p) g s) =
        determinantSlope (characterOfParams d.weight (d.exponent + s)) (((r + 1 : ℕ) : ℂ) / 2) X •
          (fun g => continuedValue ν μ d a Φ (W p) g s) +
          fun g => continuedValue ν μ d a (testDerivative Φ X) (W p) g s

theorem complexGodementContinuedLie : ComplexGodementContinuedLieStatement r := by
  intro P ν hν μ a d S W hWc hWb p hp Φ s X
  exact rightDerivative_continuedValue ν μ a d S W hWc hWb p hp Φ s X

end Langlands.Global.RankinSelbergGlobal.ComplexGodement
