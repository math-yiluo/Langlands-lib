import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonAveraging
import Langlands.AllField.Representation.GodementJacquet.AnalyticData
import Langlands.AllField.Representation.GodementJacquet.WhittakerAveraging
/-!
# Paired compact averaging for matrix functional equations

The same normalized average is transported through inverse transpose. Every
integral comparison retains an explicit convergence hypothesis.
-/

noncomputable section

namespace Langlands.AllField.GodementJacquet
open Langlands.GodementJacquet
open Langlands.AllField.GodementJacquet

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg
open scoped ENNReal NNReal Pointwise

universe uG uF uV

section NormalizedAverage



end NormalizedAverage

namespace Padic
open Langlands.GodementJacquet.Padic hiding IotaMatrixAnalyticAssertions IotaMatrixConvergesOnRight IsMatrixNormalizedGenerator MatrixAnalyticAssertions MatrixConverges MatrixConvergesOnRight MatrixFourierPair NormalizedMatrixFunctionalEquationData averagedModelCoefficient averagedModelCoefficient_apply averagedModelCoefficient_paired_integrals averagingBorelSpace averagingLocalField averagingMeasurableSpace averagingSecondCountable averagingSigmaCompact averagingTopology averagingValuativeRel coefficientIota_averagedModelCoefficient comparisonAveragingBorelSpace comparisonAveragingLocalField comparisonAveragingMeasurableSpace comparisonAveragingSecondCountable comparisonAveragingSigmaCompact comparisonAveragingTopology comparisonAveragingValuativeRel exists_compactOpen_matrixTest_invariant exists_nhds_matrixTest_invariant instBorelSpaceGeneralLinearHAddNatOfNatCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier_1 instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier_1 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instValuativeRelCarrier instValuativeRelCarrier_1 inverseTransposeOpenSubgroup iotaMatrixRationalValues isCompact_inverseTransposeOpenSubgroup jpssI2 jpssI3 jpssI3_le_jpssI2 matrixIntegral matrixIntegral_normalizedLeftAverage matrixIntegrand matrixRationalValues modelSetIntegral modelSetIntegralDual whittakerRationalValues whittakerRationalValues_subset
open Langlands.AllField.GodementJacquet.Padic
open Langlands.GodementJacquet hiding IotaMatrixAnalyticAssertions IotaMatrixConvergesOnRight IsIotaMatrixNormalizedGenerator IsMatrixNormalizedGenerator MatrixAnalyticAssertions MatrixConverges MatrixConvergesOnRight MatrixFourierPair NormalizedMatrixFunctionalEquationData iotaMatrixRationalValues jpssI2 jpssI3 matrixIntegral matrixIntegrand matrixRationalValues whittakerRationalValues
open Langlands.AllField.GodementJacquet

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance comparisonAveragingMeasurableSpace (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F) := borel _
local instance comparisonAveragingBorelSpace (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
local instance comparisonAveragingSecondCountable (n : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear (n + 1) F) :=
  (⟨⟩ : LocalFieldData F).generalLinearSecondCountableTopology (n + 1)
local instance comparisonAveragingSigmaCompact (n : ℕ) :
    SigmaCompactSpace (Langlands.GeneralLinear (n + 1) F) :=
  (⟨⟩ : LocalFieldData F).generalLinearSigmaCompactSpace (n + 1)

variable {n : ℕ}

/-- Averaging a model vector gives an actual bi-smooth matrix coefficient on
that same model representation, normalized by the subgroup's Haar mass. -/
def averagedModelCoefficient (ψ : UnitaryAdditiveCharacter F)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (hσ : IsSmooth σ) (ℓ : glFunctionals ψ n σ)
    (K : OpenSubgroup (Langlands.GeneralLinear (n + 1) F))
    (hK : IsCompact (K : Set (Langlands.GeneralLinear (n + 1) F)))
    (w : (glCoefficientModel ψ n σ ℓ).toSubmodule) :
    biSmoothMatrixCoefficients (V := (glCoefficientModel ψ n σ ℓ).toSubmodule)
      (glModelRepresentation ψ n σ ℓ) :=
  (generalLinearHaar F n |>.real (K : Set _ ) : ℂ)⁻¹ •
    ⟨biSmoothCoefficient _ (modelSetIntegralDual F ψ σ hσ ℓ K hK)
      ⟨w, glModel_isSmooth ψ n σ hσ ℓ w⟩,
      Submodule.subset_span ⟨_, _, rfl⟩⟩

@[simp]
theorem averagedModelCoefficient_apply (ψ : UnitaryAdditiveCharacter F)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (hσ : IsSmooth σ) (ℓ : glFunctionals ψ n σ)
    (K : OpenSubgroup (Langlands.GeneralLinear (n + 1) F))
    (hK : IsCompact (K : Set (Langlands.GeneralLinear (n + 1) F)))
    (w : (glCoefficientModel ψ n σ ℓ).toSubmodule)
    (g : Langlands.GeneralLinear (n + 1) F) :
    (averagedModelCoefficient F ψ σ hσ ℓ K hK w).val g =
      normalizedLeftAverage (generalLinearHaar F n) (K : Set _)
        (glModelFunction ψ n σ ℓ w) g := rfl

/-- Normalized averaging preserves an actual full-matrix integral at every
parameter where the original integrand is integrable. -/
theorem matrixIntegral_normalizedLeftAverage
    (K : OpenSubgroup (Langlands.GeneralLinear (n + 1) F))
    (hKc : IsCompact (K : Set (Langlands.GeneralLinear (n + 1) F)))
    (Φ : MatrixTestFunction n F)
    (hK : ∀ k ∈ K, (∀ M, Φ (k.val * M) = Φ M) ∧
      normalizedAbsoluteValue (⟨⟩ : LocalFieldData F) (Matrix.det k.val) = 1)
    (W : Langlands.GeneralLinear (n + 1) F → ℂ) (s : ℂ)
    (hconv : MatrixConverges F Φ s W) :
    MatrixConverges F Φ s
        (normalizedLeftAverage (generalLinearHaar F n) (K : Set _) W) ∧
      matrixIntegral F Φ s
        (normalizedLeftAverage (generalLinearHaar F n) (K : Set _) W) =
        matrixIntegral F Φ s W := by
  let μ := generalLinearHaar F n
  let abv := normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)
  let a : Langlands.GeneralLinear (n + 1) F → ℂ :=
    fun g => Φ g.val * determinantWeight abv g s
  have ha : ∀ x ∈ K, ∀ g, a (x * g) = a g := by
    intro x hx g
    obtain ⟨hΦx, hdet⟩ := hK x hx
    change Φ (x.val * g.val) * determinantWeight abv (x * g) s =
      Φ g.val * determinantWeight abv g s
    rw [hΦx, determinantWeight, determinantWeight, Units.val_mul,
      Matrix.det_mul, AbsoluteValue.map_mul, hdet, one_mul]
  have hint : Integrable (fun g => a g * W g) μ := by
    refine hconv.congr (Filter.Eventually.of_forall fun g => ?_)
    change Φ g.val * W g * determinantWeight abv g s =
      (Φ g.val * determinantWeight abv g s) * W g
    ring
  obtain ⟨hc, hv⟩ := normalizedLeftAverage_integral μ (K : Set _)
    K.isOpen.measurableSet hKc.measure_lt_top.ne
    (K.isOpen.measure_pos μ ⟨1, K.one_mem⟩).ne' a W ha hint
  have hpt (W' : Langlands.GeneralLinear (n + 1) F → ℂ) :
      GodementJacquet.matrixIntegrand abv Φ s W' = fun g => a g * W' g := by
    funext g
    simp only [GodementJacquet.matrixIntegrand, a]
    ring
  constructor
  · change Integrable (GodementJacquet.matrixIntegrand abv Φ s _) μ
    rwa [hpt]
  · change (∫ g, GodementJacquet.matrixIntegrand abv Φ s _ g ∂μ) =
      ∫ g, GodementJacquet.matrixIntegrand abv Φ s W g ∂μ
    simpa only [hpt] using hv

/-- The compact open subgroup transported by inverse transpose. -/
def inverseTransposeOpenSubgroup
    (K : OpenSubgroup (Langlands.GeneralLinear (n + 1) F)) :
    OpenSubgroup (Langlands.GeneralLinear (n + 1) F) :=
  K.comap (GeneralLinear.inverseTranspose (n + 1) F).toMonoidHom
    (GeneralLinear.continuous_inverseTranspose (n + 1) F)

/-- The transported subgroup remains compact. -/
theorem isCompact_inverseTransposeOpenSubgroup
    (K : OpenSubgroup (Langlands.GeneralLinear (n + 1) F))
    (hK : IsCompact (K : Set (Langlands.GeneralLinear (n + 1) F))) :
    IsCompact (inverseTransposeOpenSubgroup F K :
      Set (Langlands.GeneralLinear (n + 1) F)) := by
  exact ((GeneralLinear.inverseTransposeContinuous (n + 1) F).toHomeomorph.isCompact_preimage).mpr hK

/-- The actual inverse-transpose transform of the averaged coefficient is the
normalized average of the transformed model function over the transported set. -/
theorem coefficientIota_averagedModelCoefficient
    (ψ : UnitaryAdditiveCharacter F)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (hσ : IsSmooth σ) (ℓ : glFunctionals ψ n σ)
    (K : OpenSubgroup (Langlands.GeneralLinear (n + 1) F))
    (hK : IsCompact (K : Set (Langlands.GeneralLinear (n + 1) F)))
    (w : (glCoefficientModel ψ n σ ℓ).toSubmodule) :
    coefficientIota (averagedModelCoefficient F ψ σ hσ ℓ K hK w).val =
      normalizedLeftAverage (generalLinearHaar F n)
        (inverseTransposeOpenSubgroup F K : Set _)
        (coefficientIota (glModelFunction ψ n σ ℓ w)) := by
  funext g
  change (averagedModelCoefficient F ψ σ hσ ℓ K hK w).val
    (GeneralLinear.inverseTranspose (n + 1) F g) = _
  rw [averagedModelCoefficient_apply]
  exact normalizedLeftAverage_comp (generalLinearHaar F n)
    (GeneralLinear.inverseTranspose (n + 1) F)
    (generalLinearHaarSymmetries F n).2.1
    ((GeneralLinear.inverseTransposeContinuous (n + 1) F).toHomeomorph.measurableEmbedding) K K.isOpen.measurableSet _ g

/-- A single actual bi-smooth coefficient preserves both integrals, assuming
convergence of each original integrand and invariance of the respective tests. -/
theorem averagedModelCoefficient_paired_integrals
    (ψ : UnitaryAdditiveCharacter F)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (hσ : IsSmooth σ) (ℓ : glFunctionals ψ n σ)
    (K : OpenSubgroup (Langlands.GeneralLinear (n + 1) F))
    (hK : IsCompact (K : Set (Langlands.GeneralLinear (n + 1) F)))
    (Φ ΦHat : MatrixTestFunction n F)
    (hΦ : ∀ k ∈ K, (∀ M, Φ (k.val * M) = Φ M) ∧
      normalizedAbsoluteValue (⟨⟩ : LocalFieldData F) (Matrix.det k.val) = 1)
    (hΦHat : ∀ k ∈ inverseTransposeOpenSubgroup F K,
      (∀ M, ΦHat (k.val * M) = ΦHat M) ∧
      normalizedAbsoluteValue (⟨⟩ : LocalFieldData F) (Matrix.det k.val) = 1)
    (w : (glCoefficientModel ψ n σ ℓ).toSubmodule) (s t : ℂ)
    (hc : MatrixConverges F Φ s (glModelFunction ψ n σ ℓ w))
    (hcd : MatrixConverges F ΦHat t (coefficientIota (glModelFunction ψ n σ ℓ w))) :
    let f := averagedModelCoefficient F ψ σ hσ ℓ K hK w
    MatrixConverges F Φ s f.val ∧
      matrixIntegral F Φ s f.val = matrixIntegral F Φ s (glModelFunction ψ n σ ℓ w) ∧
      MatrixConverges F ΦHat t (coefficientIota f.val) ∧
      matrixIntegral F ΦHat t (coefficientIota f.val) =
        matrixIntegral F ΦHat t (coefficientIota (glModelFunction ψ n σ ℓ w)) := by
  have ho := matrixIntegral_normalizedLeftAverage F K hK Φ hΦ
    (glModelFunction ψ n σ ℓ w) s hc
  have hd := matrixIntegral_normalizedLeftAverage F (inverseTransposeOpenSubgroup F K)
    (isCompact_inverseTransposeOpenSubgroup F K hK) ΦHat hΦHat
    (coefficientIota (glModelFunction ψ n σ ℓ w)) t hcd
  have hf : (averagedModelCoefficient F ψ σ hσ ℓ K hK w).val =
      normalizedLeftAverage (generalLinearHaar F n) (K : Set _)
        (glModelFunction ψ n σ ℓ w) := by
    funext g
    exact averagedModelCoefficient_apply F ψ σ hσ ℓ K hK w g
  dsimp only
  rw [hf]
  refine ⟨ho.1, ho.2, ?_⟩
  have hi := coefficientIota_averagedModelCoefficient F ψ σ hσ ℓ K hK w
  rw [hf] at hi
  rw [hi]
  exact hd

end Padic

end Langlands.AllField.GodementJacquet
