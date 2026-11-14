import Langlands.Representation.RankinSelberg.AdjacentRankDualCompactCoefficients
import Langlands.AllField.Representation.GodementJacquet.InverseTransposeMatrixIntegral
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankCompactCoefficients
/-! The same compact-average family after Weyl/inverse-transpose transformation. -/

noncomputable section

namespace Langlands.AllField.RankinSelberg.Padic
open Langlands.RankinSelberg.Padic hiding adjacentRankCompact_middleAverage adjacentRankCompact_middleAverage_and_dual adjacentRankDualMiddleAverage adjacentRankDualMiddleAverage_eq compactCoefficientsBorel compactCoefficientsLocalField compactCoefficientsMeasurable compactCoefficientsTopology compactCoefficientsValuativeRel dualCompactFieldTopology dualCompactGroupBorel dualCompactGroupMeasurable dualCompactLocalField dualCompactValuativeRel
open Langlands.AllField.RankinSelberg.Padic
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankContinuedFormsStatement EqualRankFunctionalEquationStatement IsPadicPairGammaFactor QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement equalRankContinuedForms isEqualRankLPolynomial_characterChange_normalized normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedAbsoluteValue_det_eq_zpow normalizedDeterminantWeight_eq_spectralPoint_zpow padic_rowFourier_equivariance padic_row_instances padic_row_translate_exists zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding PadicRowFourierEquivarianceStatement padicRectangularHaarScaling padicRowFourierEquivariance padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
open scoped BigOperators

universe uF uV

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance dualCompactGroupMeasurable (r : ℕ) :
    MeasurableSpace (GeneralLinear (r + 1) F) := borel _
local instance dualCompactGroupBorel (r : ℕ) :
    BorelSpace (GeneralLinear (r + 1) F) := ⟨rfl⟩

/-- The normalized middle compact average of the actual Weyl/inverse-transpose
transform of a group function, for the unchanged canonical group Haar. -/
def adjacentRankDualMiddleAverage {r : ℕ}
    (K : OpenSubgroup (GeneralLinear (r + 1) F))
    (W : GeneralLinear (r + 1) F → ℂ)
    (g h : GeneralLinear (r + 1) F) : ℂ :=
  ((generalLinearHaar F r).real (K : Set _) : ℂ)⁻¹ *
    ∫ k in (K : Set _), dualFunction r W (g * k * h) ∂generalLinearHaar F r

/-- An inverse-transpose invariant subgroup permits the exact change of
variable in the compact average, without a Haar comparison scalar. -/
theorem adjacentRankDualMiddleAverage_eq {r : ℕ}
    (K : OpenSubgroup (GeneralLinear (r + 1) F))
    (hK : ∀ k ∈ K, inverseTranspose (r + 1) F k ∈ K)
    (W : GeneralLinear (r + 1) F → ℂ)
    (g h : GeneralLinear (r + 1) F) :
    adjacentRankDualMiddleAverage F K W g h =
      ((generalLinearHaar F r).real (K : Set _) : ℂ)⁻¹ *
        ∫ k in (K : Set _),
          W (weylLong (r + 1) F * inverseTranspose (r + 1) F g *
            k * inverseTranspose (r + 1) F h) ∂generalLinearHaar F r := by
  have hpre : (inverseTranspose (r + 1) F) ⁻¹' (K : Set _) = K := by
    ext k
    change inverseTranspose (r + 1) F k ∈ K ↔ k ∈ K
    constructor
    · intro hk
      have hh := hK _ hk
      rw [inverseTranspose_involutive] at hh
      exact hh
    · exact hK k
  have hmp := Langlands.AllField.GodementJacquet.Padic.generalLinearHaar_measurePreserving_inverseTranspose F r
  have hemb := (GodementJacquet.inverseTransposeMeasurableEquiv hmp.measurable).measurableEmbedding
  have hi := hmp.setIntegral_preimage_emb hemb
    (fun k => W (weylLong (r + 1) F * inverseTranspose (r + 1) F g *
      k * inverseTranspose (r + 1) F h)) (K : Set _)
  rw [hpre] at hi
  unfold adjacentRankDualMiddleAverage
  congr 1
  calc
    (∫ k in (K : Set _), dualFunction r W (g * k * h) ∂generalLinearHaar F r) =
        ∫ k in (K : Set _),
          W (weylLong (r + 1) F * inverseTranspose (r + 1) F g *
            inverseTranspose (r + 1) F k *
            inverseTranspose (r + 1) F h) ∂generalLinearHaar F r := by
      apply integral_congr_ae
      filter_upwards [] with k
      change W (weylLong (r + 1) F * inverseTranspose (r + 1) F (g * k * h)) = _
      simp only [map_mul, mul_assoc]
    _ = _ := hi

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- One finite family and its actual bi-smooth matrix coefficients separate
both the original and transformed middle averages. The transformed matrix
functions are precisely inverse-transpose precompositions of the original ones. -/
theorem adjacentRankCompact_middleAverage_and_dual
    (ψ : UnitaryAdditiveCharacter F) {r : ℕ}
    (σ : Representation ℂ (GeneralLinear (r + 1) F) V)
    (hσ : IsAdmissible σ) (ℓ : glFunctionals ψ r σ)
    (K : OpenSubgroup (GeneralLinear (r + 1) F))
    (hKc : IsCompact (K : Set (GeneralLinear (r + 1) F)))
    (hKι : ∀ k ∈ K, inverseTranspose (r + 1) F k ∈ K) :
    ∃ (N : ℕ) (B : Fin N → (glCoefficientModel ψ r σ ℓ).toSubmodule),
      ∀ W : (glCoefficientModel ψ r σ ℓ).toSubmodule,
        ∃ f : Fin N → GodementJacquet.biSmoothMatrixCoefficients
          (V := (glCoefficientModel ψ r σ ℓ).toSubmodule) (glModelRepresentation ψ r σ ℓ),
          (∀ g h : GeneralLinear (r + 1) F,
            ((generalLinearHaar F r).real (K : Set _) : ℂ)⁻¹ *
                (∫ k in (K : Set _), W.val.val (g * k * h)
                  ∂generalLinearHaar F r) =
              ∑ i, (B i).val.val g * (f i).val h) ∧
          ∀ g h : GeneralLinear (r + 1) F,
            adjacentRankDualMiddleAverage F K W.val.val g h =
              ∑ i, (dualModelLinearMap ψ σ ℓ (B i)).val.val g *
                GodementJacquet.coefficientIota (f i).val h := by
  obtain ⟨N, B, hB⟩ := adjacentRankCompact_middleAverage F ψ σ hσ ℓ K hKc
  refine ⟨N, B, fun W => ?_⟩
  obtain ⟨f, hf⟩ := hB W
  refine ⟨f, hf, fun g h => ?_⟩
  rw [adjacentRankDualMiddleAverage_eq F K hKι]
  exact hf (weylLong (r + 1) F * inverseTranspose (r + 1) F g)
    (inverseTranspose (r + 1) F h)

end Langlands.AllField.RankinSelberg.Padic
