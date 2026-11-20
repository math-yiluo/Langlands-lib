import Langlands.Representation.GodementJacquet.ComplexJacquetRecursionConvergence
import Langlands.Representation.Archimedean.ComplexJacquetBorel
import Langlands.Global.RankinSelberg.ComplexLocalEqualHolomorphy
import Mathlib.Analysis.Complex.CauchyIntegral

/-! # Holomorphy of the complex Jacquet recursion in the adjoining exponent -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Elementwise

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GodementJacquet

open Langlands.GeneralLinear Langlands.HarmonicAnalysis
open Langlands.Archimedean (characterOfParams)
open Langlands.Global.RankinSelbergGlobal hiding detPower
open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal
open Langlands.Global.RankinSelbergGlobal.ComplexLocalConvergence

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

variable {r : ℕ}
local notation "m" => r + 1
local notation "n" => (r + 1) + 1
local notation "H" => GeneralLinear m ℂ
local notation "G" => GeneralLinear n ℂ
local notation "U" => upperUnipotent m ℂ
local notation "R" => Matrix (Fin m) (Fin n) ℂ

/-- The logarithm of the normalized determinant modulus on complex `GL`. -/
def complexJacquetLogDet {j : ℕ} (g : GeneralLinear j ℂ) : ℝ :=
  Real.log (complexNormalizedAbs g.val.det)

theorem continuous_complexJacquetLogDet (j : ℕ) :
    Continuous (complexJacquetLogDet : GeneralLinear j ℂ → ℝ) := by
  have hdet : Continuous (fun g : GeneralLinear j ℂ => g.val.det) :=
    Units.continuous_val.comp Matrix.GeneralLinearGroup.continuous_det
  exact (hdet.norm.pow 2).log fun g => (complexNormalizedAbs_det_pos g).ne'

private theorem characterOfParams_detWeight (l : ℤ) (t s : ℂ)
    {j : ℕ} (g : GeneralLinear j ℂ) :
    complexJacquetDetWeight (characterOfParams l t).character.toMonoidHom g s =
      complexJacquetDetWeight (characterOfParams l 0).character.toMonoidHom g s *
        Complex.exp (t * (complexJacquetLogDet g : ℂ)) := by
  let z := determinant g
  have hz : 0 < ‖(z : ℂ)‖ := norm_pos_iff.mpr z.ne_zero
  have hNorm : (‖(z : ℂ)‖ : ℂ) ^ (2 * t) = Complex.exp (t * (complexJacquetLogDet g : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hz.ne'),
      ← Complex.ofReal_log hz.le]
    change Complex.exp ((Real.log ‖(z : ℂ)‖ : ℂ) * (2 * t)) =
      Complex.exp (t * (Real.log (‖(z : ℂ)‖ ^ 2) : ℂ))
    rw [Real.log_pow]
    congr 1
    push_cast
    ring
  change ((characterOfParams l t).character z : ℂ) * detPower complexNormalizedAbs g s =
    ((characterOfParams l 0).character z : ℂ) * detPower complexNormalizedAbs g s * _
  rw [(characterOfParams l t).character_eq, (characterOfParams l 0).character_eq]
  change _ * (‖(z : ℂ)‖ : ℂ) ^ (2 * t) * detPower complexNormalizedAbs g s =
    _ * (‖(z : ℂ)‖ : ℂ) ^ (2 * 0) * detPower complexNormalizedAbs g s * _
  rw [mul_zero, Complex.cpow_zero, mul_one, hNorm]
  simp only [Langlands.Archimedean.characterOfParams_weight]
  ring

/-- The adjoining spectral parameter occurs only in an exponential with a
real logarithmic coefficient. -/
theorem complexJacquetRecursionGroupKernel_exponent (a : ℂˣ) (Φ : R → ℂ) (W : H → ℂ)
    (l : ℤ) (g : G) (t : ℂ) (k : H) :
    complexJacquetRecursionGroupKernel a Φ W (characterOfParams l t).character.toMonoidHom g k =
      complexJacquetRecursionGroupKernel a Φ W (characterOfParams l 0).character.toMonoidHom g k *
        Complex.exp (t * ((complexJacquetLogDet g + complexJacquetLogDet k⁻¹ : ℝ) : ℂ)) := by
  unfold complexJacquetRecursionGroupKernel
  rw [characterOfParams_detWeight l t _ g, characterOfParams_detWeight l t _ k⁻¹,
    Complex.ofReal_add, mul_add, Complex.exp_add]
  ring

/-- With the smaller Whittaker function and rectangular test fixed, the
quotient recursion is entire in the exponent of the adjoining character. -/
theorem analyticOnNhd_complexJacquetRecursion_exponent (a : ℂˣ) (D : ComplexQuotientMeasureData r)
    (Φ : SchwartzMap R ℂ) (l : ℤ) {W : H → ℂ} (hWcont : Continuous W)
    (hU : ∀ (u : U) (k : H),
      W (u.val * k) = traceCharacter a (unipotentFourierSum r u) * W k)
    (hW : HasSimpleRootLogBound W) (g : G) :
    AnalyticOnNhd ℂ (fun t : ℂ =>
      complexJacquetRecursion a D Φ W (characterOfParams l t).character.toMonoidHom g) Set.univ := by
  let A := complexJacquetRecursionGroupKernel a Φ W (characterOfParams l 0).character.toMonoidHom g
  let B (k : H) := complexJacquetLogDet g + complexJacquetLogDet k⁻¹
  have hB : Measurable B :=
    (continuous_const.add ((continuous_complexJacquetLogDet m).comp continuous_inv)).measurable
  have hTwist (t : ℂ) :
      (fun k => A k * Complex.exp (t * (B k : ℂ))) =
        complexJacquetRecursionGroupKernel a Φ W (characterOfParams l t).character.toMonoidHom g :=
    funext fun k => (complexJacquetRecursionGroupKernel_exponent a Φ W l g t k).symm
  have hI (t : ℂ) : Integrable (fun k => A k * Complex.exp (t * (B k : ℂ))) D.groupHaar := by
    rw [hTwist]
    exact integrable_complexJacquetRecursionGroupKernel a D Φ (characterOfParams l t)
      hWcont hU hW g
  have heq :
      (fun t : ℂ => complexJacquetRecursion a D Φ W (characterOfParams l t).character.toMonoidHom g) =
        fun t => ∫ k, A k * Complex.exp (t * (B k : ℂ)) ∂D.groupHaar := by
    funext t
    rw [complexJacquetRecursion_eq_group_of_simpleRootLogBound a D Φ
      (characterOfParams l t) hWcont hU hW g, hTwist]
  rw [heq]
  exact (differentiableOn_integral_mul_cexp hB isOpen_univ fun t _ => hI t).analyticOnNhd isOpen_univ

/-- The single-exponent holomorphy assertion for the quotient recursion. -/
def ComplexJacquetRecursionExponentHolomorphyStatement : Prop :=
  ∀ (r : ℕ) (a : ℂˣ) (D : ComplexQuotientMeasureData r)
    (Φ : SchwartzMap (Matrix (Fin (r + 1)) (Fin ((r + 1) + 1)) ℂ) ℂ)
    (l : ℤ) (W : GeneralLinear (r + 1) ℂ → ℂ), Continuous W →
    (∀ (u : upperUnipotent (r + 1) ℂ) (k : GeneralLinear (r + 1) ℂ),
      W (u.val * k) = traceCharacter a (unipotentFourierSum r u) * W k) →
    HasSimpleRootLogBound W → ∀ g : GeneralLinear ((r + 1) + 1) ℂ,
      AnalyticOnNhd ℂ (fun t : ℂ =>
        complexJacquetRecursion a D Φ W (characterOfParams l t).character.toMonoidHom g) Set.univ

theorem complexJacquetRecursionExponentHolomorphy : ComplexJacquetRecursionExponentHolomorphyStatement :=
  fun _ a D Φ l _ hWcont hU hW g => analyticOnNhd_complexJacquetRecursion_exponent a D Φ l hWcont hU hW g

end Langlands.GodementJacquet
