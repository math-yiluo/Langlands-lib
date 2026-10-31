import Langlands.Representation.GodementJacquet.AnalyticData
import Langlands.Representation.RankinSelberg.HaarSymmetriesProof
import Langlands.Representation.RankinSelberg.UnequalRankBlockZeroCovariance

/-!
# Inverse-transpose substitution in transformed matrix integrals

For a group measure preserved by the inverse transpose `ι g = (g⁻¹)ᵀ`, the
matrix integrand of `coefficientIota f` composed with `ι` is
`g ↦ Φ (ι g) * f g * |det g|^(-s)`. Hence convergence and the value of the
transformed matrix integral are those of this substituted integrand.
-/

noncomputable section

namespace Langlands.GodementJacquet

open MeasureTheory HarmonicAnalysis RankinSelberg

universe uF

section General

variable {F : Type uF} [Field F] [TopologicalSpace F] {n : ℕ}

/-- The integrand obtained from the transformed matrix integrand by the
substitution `g ↦ ι g`. -/
def inverseTransposeSubstitutedIntegrand (abv : AbsoluteValue F ℝ)
    (Φ : MatrixTestFunction n F) (s : ℂ) (f : Langlands.GeneralLinear (n + 1) F → ℂ)
    (g : Langlands.GeneralLinear (n + 1) F) : ℂ :=
  Φ (GeneralLinear.inverseTranspose (n + 1) F g).val * f g * determinantWeight abv g (-s)

/-- The transformed matrix integrand at `ι g` is the substituted integrand at `g`. -/
theorem matrixIntegrand_coefficientIota_inverseTranspose (abv : AbsoluteValue F ℝ)
    (Φ : MatrixTestFunction n F) (s : ℂ) (f : Langlands.GeneralLinear (n + 1) F → ℂ)
    (g : Langlands.GeneralLinear (n + 1) F) :
    matrixIntegrand abv Φ s (coefficientIota f) (GeneralLinear.inverseTranspose (n + 1) F g) =
      inverseTransposeSubstitutedIntegrand abv Φ s f g := by
  simp only [matrixIntegrand, coefficientIota, GeneralLinear.inverseTranspose_involutive,
    determinantWeight_inverseTranspose, inverseTransposeSubstitutedIntegrand]

variable [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]

/-- The inverse transpose, given that it is measurable, as a measurable equivalence;
it is its own inverse. -/
def inverseTransposeMeasurableEquiv
    (hι : Measurable (GeneralLinear.inverseTranspose (n + 1) F)) :
    Langlands.GeneralLinear (n + 1) F ≃ᵐ Langlands.GeneralLinear (n + 1) F where
  toEquiv := (GeneralLinear.inverseTranspose (n + 1) F).toEquiv
  measurable_toFun := hι
  measurable_invFun := hι

/-- Transformed convergence is integrability of the substituted integrand. -/
theorem matrixConverges_coefficientIota_iff (abv : AbsoluteValue F ℝ)
    {μ : Measure (Langlands.GeneralLinear (n + 1) F)}
    (hμ : MeasurePreserving (GeneralLinear.inverseTranspose (n + 1) F) μ μ)
    (Φ : MatrixTestFunction n F) (s : ℂ) (f : Langlands.GeneralLinear (n + 1) F → ℂ) :
    MatrixConverges abv μ Φ s (coefficientIota f) ↔
      Integrable (inverseTransposeSubstitutedIntegrand abv Φ s f) μ := by
  have he := (inverseTransposeMeasurableEquiv hμ.measurable).measurableEmbedding
  rw [MatrixConverges, ← hμ.integrable_comp_emb he]
  have : matrixIntegrand abv Φ s (coefficientIota f) ∘
      (GeneralLinear.inverseTranspose (n + 1) F) =
      inverseTransposeSubstitutedIntegrand abv Φ s f := by
    funext g
    exact matrixIntegrand_coefficientIota_inverseTranspose abv Φ s f g
  rw [this]

/-- The transformed matrix integral is the integral of the substituted integrand. -/
theorem matrixIntegral_coefficientIota (abv : AbsoluteValue F ℝ)
    {μ : Measure (Langlands.GeneralLinear (n + 1) F)}
    (hμ : MeasurePreserving (GeneralLinear.inverseTranspose (n + 1) F) μ μ)
    (Φ : MatrixTestFunction n F) (s : ℂ) (f : Langlands.GeneralLinear (n + 1) F → ℂ) :
    matrixIntegral abv μ Φ s (coefficientIota f) =
      ∫ g, inverseTransposeSubstitutedIntegrand abv Φ s f g ∂μ := by
  have he := (inverseTransposeMeasurableEquiv hμ.measurable).measurableEmbedding
  rw [matrixIntegral, ← hμ.integral_comp he]
  simp only [matrixIntegrand_coefficientIota_inverseTranspose]

end General

namespace Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- The canonical normalized group Haar measure is preserved by inverse transpose. -/
theorem generalLinearHaar_measurePreserving_inverseTranspose (n : ℕ) :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    letI := F.canonicalTopologicalData.localField
    letI : MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := borel _
    haveI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
    MeasurePreserving (GeneralLinear.inverseTranspose (n + 1) F.Carrier)
      (generalLinearHaar F.Carrier n) (generalLinearHaar F.Carrier n) := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let : MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := borel _
  have : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  exact (generalLinearHaarSymmetries F.Carrier n).2.1

end Padic

end Langlands.GodementJacquet
