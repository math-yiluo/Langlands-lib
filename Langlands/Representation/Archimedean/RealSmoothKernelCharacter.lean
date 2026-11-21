import Langlands.HarmonicAnalysis.Distribution.GeneralLinear
import Langlands.Representation.Archimedean.RealComplexKernelTests
import Langlands.Representation.Archimedean.RealHilbertCharacter
import Langlands.Representation.Archimedean.SmoothOrbitAveraging

/-! # The real Hilbert character on smooth complex inverse kernels -/

noncomputable section

open Filter MeasureTheory
open scoped ContDiff Distributions Manifold Matrix Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

open DerivativeSmoothVectors (smoothedOperator)
open Langlands.Analysis.OperatorIdeals
open Langlands.HarmonicAnalysis.Distribution
  (transposeHomeomorph transposeHomeomorph_apply transposeHomeomorph_coe)
open Langlands.HarmonicAnalysis.RealGeneralLinearDistribution
open RealPrincipalSeriesHilbert (complexRestriction hasCompactSupport_complexRestriction)

variable {n : ℕ}

local notation "GL" => Langlands.GeneralLinear n ℝ
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "Mdl" => matrixModel ℝ n
local notation "trp" => transposeHomeomorph n ℝ

variable [MeasurableSpace (Langlands.GeneralLinear n ℝ)] [BorelSpace (Langlands.GeneralLinear n ℝ)]
  (μ : Measure (Langlands.GeneralLinear n ℝ)) [IsFiniteMeasureOnCompacts μ]

section IntegratedTest

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (R : Langlands.GeneralLinear n ℝ →* (H →L[ℂ] H)) (hR : IsContinuousRepresentation R)

private def inverseRealTestOperator (φ : Test n) : H →L[ℂ] H :=
  smoothedOperator (A := Mat) R μ hR (fun g => complexRestriction φ g⁻¹)
    ((complexRestriction φ).continuous.comp continuous_inv)
    ((hasCompactSupport_complexRestriction φ).comp_homeomorph (Homeomorph.inv GL))

private theorem inverseRealTestOperator_apply (φ : Test n) (x : H) :
    inverseRealTestOperator μ R hR φ x = ∫ g : GL, (φ (g : Mat) : ℂ) • R g x ∂μ := by
  change (∫ g : GL, complexRestriction φ (g⁻¹)⁻¹ • R g x ∂μ) = _
  simp only [inv_inv]
  rfl

/-- The bounded integrated action of a real smooth test, written as an inverse
kernel for the existing smoothing operator. -/
def realIntegratedOperator : Test n →ₗ[ℝ] H →L[ℂ] H where
  toFun := inverseRealTestOperator μ R hR
  map_add' φ ψ := by
    apply ContinuousLinearMap.ext
    intro x
    change inverseRealTestOperator μ R hR (φ + ψ) x =
      inverseRealTestOperator μ R hR φ x + inverseRealTestOperator μ R hR ψ x
    have h (y : Mat) : (φ + ψ) y = φ y + ψ y := rfl
    simp only [inverseRealTestOperator_apply, h, Complex.ofReal_add, add_smul]
    exact integral_add (integrable_realTestOrbit μ R hR φ x) (integrable_realTestOrbit μ R hR ψ x)
  map_smul' c φ := by
    apply ContinuousLinearMap.ext
    intro x
    change inverseRealTestOperator μ R hR (c • φ) x = (c : ℂ) • inverseRealTestOperator μ R hR φ x
    have h (y : Mat) : (c • φ) y = c * φ y := rfl
    simp only [inverseRealTestOperator_apply, h, Complex.ofReal_mul, mul_smul]
    exact integral_smul _ _

@[simp]
theorem realIntegratedOperator_apply (φ : Test n) (x : H) :
    realIntegratedOperator μ R hR φ x = ∫ g : GL, (φ (g : Mat) : ℂ) • R g x ∂μ :=
  inverseRealTestOperator_apply μ R hR φ x

private theorem smoothedOperator_eq_realComponents (κ : GL → ℂ)
    (hκ : Continuous κ) (hkc : HasCompactSupport κ) (φ ψ : Test n)
    (he : ∀ g : GL, κ g⁻¹ = (φ (g : Mat) : ℂ) + Complex.I * (ψ (g : Mat) : ℂ)) :
    smoothedOperator (A := Mat) R μ hR κ hκ hkc =
      realIntegratedOperator μ R hR φ + Complex.I • realIntegratedOperator μ R hR ψ := by
  apply ContinuousLinearMap.ext
  intro x
  let f : GL → H := fun g => (φ (g : Mat) : ℂ) • R g x
  let q : GL → H := fun g => (ψ (g : Mat) : ℂ) • R g x
  change (∫ g, κ g⁻¹ • R g x ∂μ) =
    realIntegratedOperator μ R hR φ x + Complex.I • realIntegratedOperator μ R hR ψ x
  have hF : Integrable f μ := integrable_realTestOrbit μ R hR φ x
  have hQ : Integrable q μ := integrable_realTestOrbit μ R hR ψ x
  calc
    _ = ∫ g, f g + Complex.I • q g ∂μ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun g => by simp only [he, add_smul, mul_smul, f, q]
    _ = (∫ g, f g ∂μ) + ∫ g, Complex.I • q g ∂μ := integral_add hF (hQ.smul Complex.I)
    _ = _ := by
      rw [integral_smul, realIntegratedOperator_apply, realIntegratedOperator_apply]

omit [MeasurableSpace (Langlands.GeneralLinear n ℝ)] [BorelSpace (Langlands.GeneralLinear n ℝ)] in
private theorem exists_realComponents_inverseKernel (κ : GL → ℂ)
    (hκ : ContMDiff Mdl 𝓘(ℝ, ℂ) ∞ κ) (hkc : HasCompactSupport κ) :
    ∃ φ ψ : Test n, ∀ g : GL, κ g⁻¹ = (φ (g : Mat) : ℂ) + Complex.I * (ψ (g : Mat) : ℂ) :=
  exists_realTests_of_compactSmoothKernel (κ ∘ Inv.inv) (hkc.comp_homeomorph (Homeomorph.inv GL))
    (hκ.comp (contMDiff_inv Mdl ∞))

variable (hTrace : ∀ φ, IsTraceClass (realIntegratedOperator μ R hR φ))

include hTrace in
/-- Trace class for the integrated real tests implies trace class for every
smooth compactly supported complex inverse kernel. -/
theorem isTraceClass_smoothedOperator_of_realTests (κ : GL → ℂ)
    (hκ : ContMDiff Mdl 𝓘(ℝ, ℂ) ∞ κ) (hkc : HasCompactSupport κ) :
    IsTraceClass (smoothedOperator (A := Mat) R μ hR κ hκ.continuous hkc) := by
  obtain ⟨φ, ψ, h⟩ := exists_realComponents_inverseKernel κ hκ hkc
  rw [smoothedOperator_eq_realComponents μ R hR κ hκ.continuous hkc φ ψ h]
  exact isTraceClass_add _ _ (hTrace φ) (isTraceClass_smul Complex.I _ (hTrace ψ))

omit [MeasurableSpace (Langlands.GeneralLinear n ℝ)] [BorelSpace (Langlands.GeneralLinear n ℝ)] in
private theorem transpose_comm_inv (g : GL) : trp g⁻¹ = (trp g)⁻¹ := by
  simp only [transposeHomeomorph_apply, map_inv, inv_inv]

/-- Transpose invariance of the real-test character gives trace class and the same
trace value for the ordinary-transposed complex inverse kernel. -/
theorem traceClass_and_trace_transpose_of_realHilbertCharacter
    (hTrans : IsTransposeInvariant
      (realHilbertCharacter μ R hR (realIntegratedOperator μ R hR)
        (realIntegratedOperator_apply μ R hR) hTrace))
    (κ : GL → ℂ) (hκ : ContMDiff Mdl 𝓘(ℝ, ℂ) ∞ κ) (hkc : HasCompactSupport κ) :
    IsTraceClass (smoothedOperator (A := Mat) R μ hR (κ ∘ trp)
      (hκ.continuous.comp (trp).continuous) (hkc.comp_homeomorph trp)) ∧
    operatorTrace (smoothedOperator (A := Mat) R μ hR (κ ∘ trp)
      (hκ.continuous.comp (trp).continuous) (hkc.comp_homeomorph trp)) =
    operatorTrace (smoothedOperator (A := Mat) R μ hR κ hκ.continuous hkc) := by
  obtain ⟨φ, ψ, h⟩ := exists_realComponents_inverseKernel κ hκ hkc
  have ht (g : GL) : (κ ∘ trp) g⁻¹ =
      (transposeTest φ (g : Mat) : ℂ) + Complex.I * (transposeTest ψ (g : Mat) : ℂ) := by
    rw [Function.comp_apply, transpose_comm_inv, h]
    simp only [transposeHomeomorph_coe, transposeTest_apply]
  rw [smoothedOperator_eq_realComponents μ R hR _ _ _ _ _ ht,
    smoothedOperator_eq_realComponents μ R hR _ _ _ _ _ h]
  refine ⟨isTraceClass_add _ _ (hTrace (transposeTest φ))
    (isTraceClass_smul Complex.I _ (hTrace (transposeTest ψ))), ?_⟩
  have hTest (χ : Test n) : operatorTrace (realIntegratedOperator μ R hR (transposeTest χ)) =
      operatorTrace (realIntegratedOperator μ R hR χ) := hTrans χ
  rw [operatorTrace_add _ _ (hTrace (transposeTest φ))
      (isTraceClass_smul Complex.I _ (hTrace (transposeTest ψ))),
    operatorTrace_add _ _ (hTrace φ) (isTraceClass_smul Complex.I _ (hTrace ψ)),
    operatorTrace_smul _ _ (hTrace (transposeTest ψ)), operatorTrace_smul _ _ (hTrace ψ),
    hTest φ, hTest ψ]

end IntegratedTest
end Langlands.Archimedean
