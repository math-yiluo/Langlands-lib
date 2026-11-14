import Langlands.Representation.RankinSelberg.AdjacentRankCompactMatrixIntegrability
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonGLAdditive
noncomputable section

open MeasureTheory
open scoped BigOperators NNReal ENNReal

namespace Langlands.AllField.RankinSelberg.AdjacentCompactMatrix
open Langlands.RankinSelberg.AdjacentCompactMatrix hiding integrable_natWeight_of_compact_bound matrixZeroExtension matrixZeroExtension_apply matrixZeroExtension_of_not_mem_range measurable_matrixZeroExtension transferBorel transferGLBorel transferGLMeasurable transferLocalField transferMeasurable transferSecondCountable transferSigmaCompact transferT2 transferTopology transferValuativeRel
open Langlands.AllField.RankinSelberg.AdjacentCompactMatrix
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement diagonalConj_map exists_rankOneCutoff exists_rankOneEmbedding_support lastRowCompactOrbit normalizedAbsoluteValue normalizedAbsoluteValue_apply rankOneModelValues_subset_whittakerRationalValues singleton_modulus_real zeroRowLastRowCutoff
open Langlands.AllField.RankinSelberg

open Langlands.HarmonicAnalysis hiding PadicSelfDualMeasureExistsStatement padicLatticeGeometry padicRectangularHaarScaling padicScalarHaarScaling padicSelfDualMeasureExists
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding MirabolicUnitTestStatement mirabolicUnitTest
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear hiding padic_exists_ne_zero_mem_nhds_zero
open Langlands.AllField.GeneralLinear

universe uF uV
variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance transferT2 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance transferSecondCountable : SecondCountableTopology F :=
  (⟨⟩ : LocalFieldData F).secondCountableTopology
local instance transferSigmaCompact : SigmaCompactSpace F := (⟨⟩ : LocalFieldData F).sigmaCompactSpace
local instance transferMeasurable : MeasurableSpace F := borel _
local instance transferBorel : BorelSpace F := ⟨rfl⟩
local instance transferGLMeasurable (n : ℕ) : MeasurableSpace (GeneralLinear (n + 1) F) := borel _
local instance transferGLBorel (n : ℕ) : BorelSpace (GeneralLinear (n + 1) F) := ⟨rfl⟩

local notation "abv" => normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)

/-- Extend a GL function by zero to all square matrices. -/
def matrixZeroExtension (r : ℕ) (f : GeneralLinear (r + 1) F → ℂ) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) F → ℂ :=
  Function.extend (Units.val : GeneralLinear (r + 1) F →
    Matrix (Fin (r + 1)) (Fin (r + 1)) F) f (fun _ => 0)

theorem matrixZeroExtension_apply (r : ℕ)
    (f : GeneralLinear (r + 1) F → ℂ)
    (g : GeneralLinear (r + 1) F) :
    matrixZeroExtension F r f g.val = f g :=
  Units.val_injective.extend_apply f (fun _ => 0) g

theorem matrixZeroExtension_of_not_mem_range (r : ℕ)
    (f : GeneralLinear (r + 1) F → ℂ)
    (X : Matrix (Fin (r + 1)) (Fin (r + 1)) F)
    (hX : X ∉ Set.range (Units.val : GeneralLinear (r + 1) F →
      Matrix (Fin (r + 1)) (Fin (r + 1)) F)) :
    matrixZeroExtension F r f X = 0 :=
  Function.extend_apply' f (fun _ => 0) X hX

theorem measurable_matrixZeroExtension (r : ℕ)
    (f : GeneralLinear (r + 1) F → ℂ) (hf : Measurable f) :
    Measurable (matrixZeroExtension F r f) :=
  (isOpenEmbedding_generalLinear_val (K := F) (r + 1)).measurableEmbedding.measurable_extend
    hf measurable_const

/-- A continuous GL function that is bounded and supported over a compact matrix
set is integrable after multiplication by the natural determinant density. -/
theorem integrable_natWeight_of_compact_bound (ν : AdditiveHaarMeasure F)
    (r : ℕ) (f : GeneralLinear (r + 1) F → ℂ) (hf : Continuous f)
    (K : Set (Matrix (Fin (r + 1)) (Fin (r + 1)) F)) (hK : IsCompact K)
    (hzero : ∀ g : GeneralLinear (r + 1) F, g.val ∉ K → f g = 0)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ g : GeneralLinear (r + 1) F, g.val ∈ K → ‖f g‖ ≤ C) :
    Integrable (fun g : GeneralLinear (r + 1) F =>
      determinantWeight abv g (r + 1 : ℕ) * f g) (generalLinearHaar F r) := by
  classical
  let μ := rectangularMeasure ν (r + 1) (r + 1)
  let A := matrixZeroExtension F r f
  have hAm : Measurable A := measurable_matrixZeroExtension F r f hf.measurable
  have hA (g : GeneralLinear (r + 1) F) : A g.val = f g :=
    matrixZeroExtension_apply F r f g
  have hAzero (X : Matrix (Fin (r + 1)) (Fin (r + 1)) F) (hX : X ∉ K) :
      A X = 0 := by
    by_cases hin : X ∈ Set.range (Units.val : GeneralLinear (r + 1) F →
        Matrix (Fin (r + 1)) (Fin (r + 1)) F)
    · obtain ⟨g, rfl⟩ := hin
      rw [hA]
      exact hzero g hX
    · exact matrixZeroExtension_of_not_mem_range F r f X hin
  have hAbound (X : Matrix (Fin (r + 1)) (Fin (r + 1)) F) : ‖A X‖ ≤ C := by
    by_cases hin : X ∈ Set.range (Units.val : GeneralLinear (r + 1) F →
        Matrix (Fin (r + 1)) (Fin (r + 1)) F)
    · obtain ⟨g, rfl⟩ := hin
      rw [hA]
      by_cases hg : g.val ∈ K
      · exact hbound g hg
      · rw [hzero g hg, norm_zero]
        exact hC
    · rw [show A X = 0 from matrixZeroExtension_of_not_mem_range F r f X hin, norm_zero]
      exact hC
  have hAi : Integrable A μ :=
    (IntegrableOn.of_bound (hK.measure_lt_top (μ := μ)) hAm.aestronglyMeasurable C
      (Filter.Eventually.of_forall hAbound)).integrable_of_forall_notMem_eq_zero hAzero
  have hi := (Langlands.AllField.RankinSelberg.GLDeterminantDensity.integrable_generalLinearHaar_natWeight_iff F ν r A).2
    (hAi.mono_measure Measure.restrict_le_self)
  simpa only [hA] using hi

end Langlands.AllField.RankinSelberg.AdjacentCompactMatrix
