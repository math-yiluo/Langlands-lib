import Langlands.HarmonicAnalysis.CharacterTransport
import Langlands.Representation.Archimedean.MatrixTraceTestCasimir
import Langlands.Representation.Archimedean.UnitaryMatrixCasimir
import Langlands.Representation.Archimedean.UnitaryWhittakerDistribution

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Langlands.GeneralLinear Langlands.HarmonicAnalysis Langlands.Whittaker
open scoped Manifold ContDiff Distributions Matrix.Norms.Operator InnerProductSpace ComplexConjugate

namespace Langlands.Archimedean

universe uF uE

variable {F : Type uF} [RCLike F] {n : ℕ} {E : Type uE}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

local notation "M" => Matrix (Fin n) (Fin n) F
local notation "D" => 𝓓(matrixUnitsOpen F n, ℂ)
local notation "I" => matrixModel F n

variable [MeasurableSpace (Langlands.GeneralLinear n F)] [BorelSpace (Langlands.GeneralLinear n F)]
  (μ : Measure (Langlands.GeneralLinear n F)) [μ.IsHaarMeasure] [μ.IsInvInvariant]
  (π : Langlands.GeneralLinear n F →* (E →L[ℂ] E)) (hπ : IsContinuousRepresentation π)
  (hπu : ∀ g v w, inner ℂ (π g v) (π g w) = inner ℂ v w)
  (ℓ₀ ℓ₁ : smoothVectors (matrixModel F n) π →ₗ[ℂ] ℂ)
  (h₀ : IsContinuousOnSmoothVectors (matrixModel F n) π ℓ₀)
  (h₁ : IsContinuousOnSmoothVectors (matrixModel F n) π ℓ₁)

/-- The scalar trace contraction on the smooth vectors gives the eigenvalue
of the corresponding matrix test-function distribution. -/
theorem unitaryWhittakerDistribution_Casimir (c : ℂ)
    (hc : ∀ v, matrixSmoothTraceCasimir π v = c • v) (f : D) :
    unitaryWhittakerDistribution μ π hπ hπu ℓ₁ h₁ ℓ₀ h₀ (matrixTraceTestCasimir F n f) =
      conj c * unitaryWhittakerDistribution μ π hπ hπu ℓ₁ h₁ ℓ₀ h₀ f := by
  classical
  let restrictTest := matrixTestFunctionKernelEquiv (F := F) (n := n)
  let b := matrixTraceUnit F n
  let d := matrixTraceDualUnit F n
  let testWord i := matrixRightTestWord [b i, d i] f
  have hTest : matrixTraceTestCasimir F n f = ∑ i, testWord i := by
    apply TestFunction.ext
    intro x
    rw [sum_apply]
    by_cases hx : IsUnit x
    · obtain ⟨g, rfl⟩ := hx
      rw [matrixTraceTestCasimir_apply, matrixTraceCasimir_eq_right f.contDiff g]
      rfl
    · rw [TestFunction.zero_on_compl _ hx]
      exact (Finset.sum_eq_zero fun i _ => (testWord i).zero_on_compl hx).symm
  let φ := adjointGardingKernel (restrictTest f)
  let φi i := adjointGardingKernel (restrictTest (testWord i))
  have hKernel : adjointGardingKernel (restrictTest (matrixTraceTestCasimir F n f)) =
      ∑ i, φi i := by
    change adjointGardingKernelEquiv (restrictTest (matrixTraceTestCasimir F n f)) = _
    rw [hTest, map_sum, map_sum]
    rfl
  have hAverage (v : E) :
      matrixSmoothTraceCasimir π (gardingIntegralLinearMap μ π hπ φ v) =
        ∑ i, gardingIntegralLinearMap μ π hπ (φi i) v := by
    rw [matrixSmoothTraceCasimir_apply]
    apply Finset.sum_congr rfl
    intro i _
    apply Subtype.ext
    change iteratedLieDerivative I π [b i, d i] (∫ x, φ.val x • π x v ∂μ) =
      ∫ x, (φi i).val x • π x v ∂μ
    rw [iteratedLieDerivative_gardingIntegral μ π hπ φ.val φ.property.1 φ.property.2 v,
      gardingKernelWord_adjoint_restrict]
  have hRegularization :
      unitaryRegularizationSmooth μ π hπ hπu ℓ₁ h₁
          (restrictTest (matrixTraceTestCasimir F n f)) =
        conj c • unitaryRegularizationSmooth μ π hπ hπu ℓ₁ h₁ (restrictTest f) := by
    apply Subtype.ext
    apply ext_inner_right ℂ
    intro v
    simp only [Submodule.coe_smul, unitaryRegularizationSmooth_coe, inner_smul_left,
      starRingEnd_self_apply, inner_unitaryRegularization]
    let L := gardingFunctionalLinearMap μ π hπ (norm_apply_of_preserves_inner π hπu) ℓ₁ h₁
    change L (adjointGardingKernel (restrictTest (matrixTraceTestCasimir F n f))) v =
      c * ℓ₁ (gardingIntegralLinearMap μ π hπ φ v)
    rw [hKernel, map_sum, sum_apply]
    change ∑ i, ℓ₁ (gardingIntegralLinearMap μ π hπ (φi i) v) = _
    rw [← map_sum, ← hAverage, hc, map_smul, smul_eq_mul]
  simp only [unitaryWhittakerDistribution_apply, unitaryWhittakerCoefficient_apply]
  change ℓ₀ (unitaryRegularizationSmooth μ π hπ hπu ℓ₁ h₁
    (restrictTest (matrixTraceTestCasimir F n f))) = _
  rw [hRegularization, map_smul, smul_eq_mul]

section Covariance

variable {r : ℕ}

local notation "U" => upperUnipotent (r + 1) F
local notation "Tests" => 𝓓(matrixUnitsOpen F (r + 1), ℂ)

private theorem standardCharacter_scale_neg_one (ψ : UnitaryAdditiveCharacter F) (u : U) :
    standardCharacter (ψ.scale (-1)) r u = (standardCharacter ψ r u)⁻¹ := by
  change scaledStandardCharacter ψ (-1) r u = _
  rw [scaledStandardCharacter_neg_one]
  rfl

/-- Positive pullback on both sides of the coefficient has the character of
the additive argument with its sign reversed. -/
theorem unitaryWhittakerDistribution_covariance
    [MeasurableSpace (Langlands.GeneralLinear (r + 1) F)]
    [BorelSpace (Langlands.GeneralLinear (r + 1) F)]
    {μ : Measure (Langlands.GeneralLinear (r + 1) F)}
    [μ.IsHaarMeasure] [μ.IsInvInvariant] [μ.IsMulRightInvariant]
    {π : Langlands.GeneralLinear (r + 1) F →* (E →L[ℂ] E)}
    (hπ : IsContinuousRepresentation π)
    (hπu : ∀ g v w, inner ℂ (π g v) (π g w) = inner ℂ v w)
    (ψ : UnitaryAdditiveCharacter F)
    {ℓ₀ ℓ₁ : smoothVectors (matrixModel F (r + 1)) π →ₗ[ℂ] ℂ}
    (hW₀ : IsWhittakerFunctional (matrixModel F (r + 1)) π U (standardCharacter ψ r) ℓ₀)
    (hW₁ : IsWhittakerFunctional (matrixModel F (r + 1)) π U (standardCharacter ψ r) ℓ₁)
    (u v : U) (f g : Tests)
    (hg : ∀ x, g x = f (u.val.val * x * v.val.val)) :
    unitaryWhittakerDistribution μ π hπ hπu ℓ₁ hW₁.1 ℓ₀ hW₀.1 g =
      ((standardCharacter (ψ.scale (-1)) r u : ℂ) *
        (standardCharacter (ψ.scale (-1)) r v : ℂ)) *
      unitaryWhittakerDistribution μ π hπ hπu ℓ₁ hW₁.1 ℓ₀ hW₀.1 f := by
  have he : matrixTestFunctionKernelEquiv g =
      gardingKernelLeft u⁻¹.val (gardingKernelRight v.val (matrixTestFunctionKernelEquiv f)) := by
    apply Subtype.ext
    funext x
    change g x.val = f ((u⁻¹.val⁻¹ * x * v.val).val)
    rw [hg]
    rfl
  simp only [unitaryWhittakerDistribution_apply]
  rw [he, unitaryWhittakerCoefficient_left μ π hπ hπu ℓ₀ ℓ₁ hW₁.1 hW₀ (u⁻¹),
    unitaryWhittakerCoefficient_right μ π hπ hπu ℓ₀ ℓ₁ hW₁ v, map_inv,
    ← Complex.inv_eq_conj (norm_standardCharacter ψ r v),
    standardCharacter_scale_neg_one, standardCharacter_scale_neg_one]
  simp only [Units.val_inv_eq_inv_val, mul_assoc]

end Covariance

end Langlands.Archimedean
