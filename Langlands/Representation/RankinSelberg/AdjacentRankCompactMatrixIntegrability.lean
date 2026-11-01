import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonGLAdditive

noncomputable section

open MeasureTheory
open scoped BigOperators NNReal ENNReal

namespace Langlands.RankinSelberg.AdjacentCompactMatrix

open HarmonicAnalysis Whittaker GeneralLinear

universe uF uV
variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance transferTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance transferValuativeRel : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance transferLocalField : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance transferT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance transferSecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance transferSigmaCompact : SigmaCompactSpace F.Carrier := F.canonicalTopologicalData.sigmaCompactSpace
local instance transferMeasurable : MeasurableSpace F.Carrier := borel _
local instance transferBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance transferGLMeasurable (n : ℕ) : MeasurableSpace (GeneralLinear (n + 1) F.Carrier) := borel _
local instance transferGLBorel (n : ℕ) : BorelSpace (GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance transferGLLocallyCompact (n : ℕ) : LocallyCompactSpace (GeneralLinear (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearLocallyCompactSpace (n + 1)
local instance transferGLSecondCountable (n : ℕ) : SecondCountableTopology (GeneralLinear (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology (n + 1)

local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData

/-- Extend a GL function by zero to all square matrices. -/
def matrixZeroExtension (r : ℕ) (f : GeneralLinear (r + 1) F.Carrier → ℂ) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) F.Carrier → ℂ :=
  Function.extend (Units.val : GeneralLinear (r + 1) F.Carrier →
    Matrix (Fin (r + 1)) (Fin (r + 1)) F.Carrier) f (fun _ => 0)

theorem matrixZeroExtension_apply (r : ℕ)
    (f : GeneralLinear (r + 1) F.Carrier → ℂ)
    (g : GeneralLinear (r + 1) F.Carrier) :
    matrixZeroExtension F r f g.val = f g :=
  Units.val_injective.extend_apply f (fun _ => 0) g

theorem matrixZeroExtension_of_not_mem_range (r : ℕ)
    (f : GeneralLinear (r + 1) F.Carrier → ℂ)
    (X : Matrix (Fin (r + 1)) (Fin (r + 1)) F.Carrier)
    (hX : X ∉ Set.range (Units.val : GeneralLinear (r + 1) F.Carrier →
      Matrix (Fin (r + 1)) (Fin (r + 1)) F.Carrier)) :
    matrixZeroExtension F r f X = 0 :=
  Function.extend_apply' f (fun _ => 0) X hX

theorem measurable_matrixZeroExtension (r : ℕ)
    (f : GeneralLinear (r + 1) F.Carrier → ℂ) (hf : Measurable f) :
    Measurable (matrixZeroExtension F r f) :=
  (isOpenEmbedding_generalLinear_val (K := F.Carrier) (r + 1)).measurableEmbedding.measurable_extend
    hf measurable_const

/-- A continuous GL function that is bounded and supported over a compact matrix
set is integrable after multiplication by the natural determinant density. -/
theorem integrable_natWeight_of_compact_bound (ν : AdditiveHaarMeasure F.Carrier)
    (r : ℕ) (f : GeneralLinear (r + 1) F.Carrier → ℂ) (hf : Continuous f)
    (K : Set (Matrix (Fin (r + 1)) (Fin (r + 1)) F.Carrier)) (hK : IsCompact K)
    (hzero : ∀ g : GeneralLinear (r + 1) F.Carrier, g.val ∉ K → f g = 0)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ g : GeneralLinear (r + 1) F.Carrier, g.val ∈ K → ‖f g‖ ≤ C) :
    Integrable (fun g : GeneralLinear (r + 1) F.Carrier =>
      determinantWeight abv g (r + 1 : ℕ) * f g) (generalLinearHaar F.Carrier r) := by
  classical
  let μ := rectangularMeasure ν (r + 1) (r + 1)
  let A := matrixZeroExtension F r f
  have hAm : Measurable A := measurable_matrixZeroExtension F r f hf.measurable
  have hA (g : GeneralLinear (r + 1) F.Carrier) : A g.val = f g :=
    matrixZeroExtension_apply F r f g
  have hAzero (X : Matrix (Fin (r + 1)) (Fin (r + 1)) F.Carrier) (hX : X ∉ K) :
      A X = 0 := by
    by_cases hin : X ∈ Set.range (Units.val : GeneralLinear (r + 1) F.Carrier →
        Matrix (Fin (r + 1)) (Fin (r + 1)) F.Carrier)
    · obtain ⟨g, rfl⟩ := hin
      rw [hA]
      exact hzero g hX
    · exact matrixZeroExtension_of_not_mem_range F r f X hin
  have hAbound (X : Matrix (Fin (r + 1)) (Fin (r + 1)) F.Carrier) : ‖A X‖ ≤ C := by
    by_cases hin : X ∈ Set.range (Units.val : GeneralLinear (r + 1) F.Carrier →
        Matrix (Fin (r + 1)) (Fin (r + 1)) F.Carrier)
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
  have hi := (GLDeterminantDensity.integrable_generalLinearHaar_natWeight_iff F ν r A).2
    (hAi.mono_measure Measure.restrict_le_self)
  simpa only [hA] using hi

end Langlands.RankinSelberg.AdjacentCompactMatrix
