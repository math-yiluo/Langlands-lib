import Langlands.Representation.RankinSelberg.TwoBlockDominantDualRectangles
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantRectangleHaar
/-!
# Signed exchange of the two dominant rectangles

The coordinate map needed for the strictly dominant reversed-dual calculation
exchanges the rectangles and applies negative transpose with both indices reversed.
It preserves the exact product of every supplied additive Haar measure.
This module does not compare the large-group matrices or their scalar kernels.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular
open Langlands.RankinSelberg.TwoBlockDominantRectangular hiding dualRectangleBorel dualRectangleLocalField dualRectangleMatrixBorel dualRectangleMatrixSecondCountable dualRectangleMeasurable dualRectangleProductBorel dualRectangleSecondCountable dualRectangleTopology dualRectangleValuation integrable_rectangleChange_iff integral_dualRectangleEquiv integral_rectangleChange measurePreserving_dualRectangleEquiv measurePreserving_rectangleChange rectangleChangeHomeomorph rectangleHaarBorel rectangleHaarLocalField rectangleHaarMeasurable rectangleHaarSecondCountable rectangleHaarTopology rectangleHaarValuation rectangleMatrixBorel rectangleMatrixSecondCountable rectangleMeasure rectangleMeasure_sigmaFinite rectanglesBorel
open Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis

universe uF uE

section Coordinates

variable {K : Type uF} [AddCommGroup K]

section Topology


end Topology

end Coordinates

section ScalarMeasure



-- This cylinder proof generalizes the private `measurePreserving_rho` argument
-- in the published `TwoBlockDualSectionJacquetProof` to reusable coordinates.

end ScalarMeasure

section PadicMeasure

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance dualRectangleSecondCountable : SecondCountableTopology F :=
  (⟨⟩ : LocalFieldData F).secondCountableTopology
local instance dualRectangleMeasurable : MeasurableSpace F := borel F
local instance dualRectangleBorel : BorelSpace F := ⟨rfl⟩
local instance dualRectangleMatrixSecondCountable (a b : ℕ) :
    SecondCountableTopology (Matrix (Fin a) (Fin b) F) :=
  inferInstanceAs (SecondCountableTopology (Fin a → Fin b → F))
local instance dualRectangleMatrixBorel (a b : ℕ) :
    BorelSpace (Matrix (Fin a) (Fin b) F) :=
  inferInstanceAs (BorelSpace (Fin a → Fin b → F))
local instance dualRectangleProductBorel (m : Fin 2 → ℕ) (j k : ℕ) :
    BorelSpace (Rectangles m j k F) :=
  inferInstanceAs (BorelSpace
    (Matrix (Fin (m 0 + 1)) (Fin k) F ×
      Matrix (Fin j) (Fin (m 1 + 1)) F))

/-- The signed rectangle exchange preserves the exact supplied product Haar.
No self-duality, nontrivial character, or positivity of `j,k` is required. -/
theorem measurePreserving_dualRectangleEquiv
    (m : Fin 2 → ℕ) (j k : ℕ) (ν : AdditiveHaarMeasure F) :
    MeasurePreserving (dualRectangleEquiv (K := F) m j k)
      (rectangleMeasure F (fun i => m i.rev) k j ν)
      (rectangleMeasure F m j k ν) := by
  have hx := measurePreserving_signedReverseTranspose ν (m 0 + 1) k
  have hy := measurePreserving_signedReverseTranspose ν j (m 1 + 1)
  exact (hx.prod hy).comp (Measure.measurePreserving_swap)

/-- Total Bochner change of variables for the two actual rectangle products. -/
theorem integral_dualRectangleEquiv
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (m : Fin 2 → ℕ) (j k : ℕ) (ν : AdditiveHaarMeasure F)
    (φ : Rectangles m j k F → E) :
    (∫ z, φ (dualRectangleEquiv m j k z)
      ∂rectangleMeasure F (fun i => m i.rev) k j ν) =
        ∫ z, φ z ∂rectangleMeasure F m j k ν :=
  (measurePreserving_dualRectangleEquiv F m j k ν).integral_comp
    (dualRectangleHomeomorph m j k).measurableEmbedding φ

end PadicMeasure

end Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular
