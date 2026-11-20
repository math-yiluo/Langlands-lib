import Langlands.Global.RankinSelberg.ComplexGodementStandardGrowth
import Langlands.Global.RankinSelberg.ComplexSquareZetaPositiveDiagonal

/-! # Absolute convergence of complex square matrix zeta integrals -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator SchwartzMap

namespace Langlands.Global.RankinSelbergGlobal.ComplexSquareZeta

open ArchimedeanLocal (complexNormalizedAbs)
open ComplexGodement (exists_height_bound_standard normPower)
open ComplexMatrixSchwartz (complexMatrixSchwartzConvergence)
open Langlands.Archimedean Langlands.Archimedean.ComplexGeneralLinearHaarDensity
open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

local instance squareConvergenceGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear n ℂ) := borel _
local instance squareConvergenceGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear n ℂ) := ⟨rfl⟩
local instance squareConvergenceGLSecondCountable (n : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear n ℂ) :=
  Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology

variable {n : ℕ}
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "Mat" => Matrix (Fin n) (Fin n) ℂ

/-- The complex determinant weight is continuous on the invertible locus. -/
theorem continuous_detNormPower (p : ℂ) : Continuous (fun g : G => normPower p (determinant g)) := by
  change Continuous (fun g : G => ((complexNormalizedAbs g.val.det : ℝ) : ℂ) ^ p)
  have hdet : Continuous (fun g : G => g.val.det) := Units.continuous_val.matrix_det
  have h : Continuous (fun g : G => (complexNormalizedAbs g.val.det : ℂ)) :=
    Complex.continuous_ofReal.comp (hdet.norm.pow 2)
  exact h.cpow continuous_const fun g => Complex.ofReal_mem_slitPlane.mpr
    (pow_pos (norm_pos_iff.mpr g.det_ne_zero) 2)

/-- A common integrable majorant for square zeta kernels with a polynomial height bound. -/
theorem integrable_height_detNormPower (μ : Measure G) [μ.IsHaarMeasure] (M : ℕ)
    (Φ : 𝓢(Mat, ℂ)) (p : ℂ) (hp : (n : ℝ) + M ≤ p.re) :
    Integrable (fun g => (complexMatrixHeight g ^ M : ℝ) * Φ g.val * normPower p (determinant g)) μ := by
  have h := complexMatrixSchwartzConvergence n M Φ p hp
  rw [Measure.isMulLeftInvariant_eq_smul μ (complexGeneralLinearHaar n)]
  exact h.smul_measure_nnreal

/-- Integrability of the square zeta kernel follows from the polynomial height bound
on its coefficient. -/
theorem integrable_zetaKernel_of_height_bound (μ : Measure G) [μ.IsHaarMeasure] (Φ : 𝓢(Mat, ℂ))
    {f : G → ℂ} (hf : Continuous f) {M : ℕ} {C : ℝ}
    (hbound : ∀ g, ‖f g‖ ≤ C * complexMatrixHeight g ^ M) (s : ℂ)
    (hs : (n : ℝ) + M ≤ (s + ((n : ℂ) - 1) / 2).re) : Integrable (zetaKernel Φ f s) μ := by
  let p := s + ((n : ℂ) - 1) / 2
  have h := integrable_height_detNormPower μ M Φ p hs
  have hc : Continuous (zetaKernel Φ f s) :=
    ((Φ.continuous.comp Units.continuous_val).mul hf).mul (continuous_detNormPower p)
  refine (h.norm.const_mul C).mono' hc.aestronglyMeasurable ?_
  filter_upwards with g
  have hH : 0 ≤ complexMatrixHeight g := by unfold complexMatrixHeight; positivity
  let a := normPower p (determinant g)
  change ‖Φ g.val * f g * a‖ ≤ C * ‖(complexMatrixHeight g ^ M : ℝ) * Φ g.val * a‖
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hH _)]
  calc
    _ ≤ ‖Φ g.val‖ * (C * complexMatrixHeight g ^ M) * ‖a‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hbound g) (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by ring

/-- The square zeta integral converges absolutely for every Schwartz test and standard vector
in a right half-plane depending only on the inducing characters. -/
def ComplexSquareZetaConvergenceStatement : Prop :=
  0 < n → ∀ ds : Fin n → ComplexCharacterData, ∃ M : ℕ,
    ∀ (μ : Measure G) [μ.IsHaarMeasure] (Φ : 𝓢(Mat, ℂ)) (f : G → ℂ),
      f ∈ complexStandardModule n (List.ofFn ds) → ∀ s : ℂ,
      (n : ℝ) + M ≤ (s + ((n : ℂ) - 1) / 2).re → Integrable (zetaKernel Φ f s) μ

theorem complexSquareZetaConvergence : ComplexSquareZetaConvergenceStatement (n := n) := by
  intro hn ds
  obtain ⟨M, hM⟩ := exists_height_bound_standard hn (List.ofFn ds) List.length_ofFn
  refine ⟨M, fun μ _ Φ f hf s hs => ?_⟩
  obtain ⟨C, _, hC⟩ := hM f hf
  exact integrable_zetaKernel_of_height_bound μ Φ hf.1.continuous hC s hs

end Langlands.Global.RankinSelbergGlobal.ComplexSquareZeta
