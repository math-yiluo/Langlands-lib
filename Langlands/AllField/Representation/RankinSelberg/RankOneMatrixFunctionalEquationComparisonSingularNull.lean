import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonSingularNull
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonGLDensity
import Langlands.LocalField.NonzeroParameter
/-! # The singular matrix locus has additive Haar measure zero -/

noncomputable section

namespace Langlands.AllField.RankinSelberg.GLDeterminantDensity
open Langlands.RankinSelberg.GLDeterminantDensity hiding padic_exists_weightedRestriction_eq_generalLinearHaar padic_weightedRestriction_isHaar rectangularMeasure_ae_det_ne_zero rectangularMeasure_restrict_generalLinear singularNullBorelSpace singularNullLocalField singularNullMeasurableSpace singularNullPuncturedNhds singularNullSecondCountable singularNullSigmaCompact singularNullT2 singularNullTopology singularNullValuativeRel
open Langlands.AllField.RankinSelberg.GLDeterminantDensity
open Langlands.RankinSelberg hiding LastRowCompactOrbitStatement lastRowCompactOrbit
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory _root_.Topology
open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open scoped NNReal ENNReal

universe uK uF

section General

variable {K : Type uK} [Field K]

variable [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
  [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K]

end General

section CanonicalPadic

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance singularNullT2 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance singularNullSecondCountable : SecondCountableTopology F :=
  (⟨⟩ : LocalFieldData F).secondCountableTopology
local instance singularNullSigmaCompact : SigmaCompactSpace F := (⟨⟩ : LocalFieldData F).sigmaCompactSpace
local instance singularNullMeasurableSpace : MeasurableSpace F := borel _
local instance singularNullBorelSpace : BorelSpace F := ⟨rfl⟩
local instance singularNullPuncturedNhds : (𝓝[≠] (0 : F)).NeBot :=
  Langlands.LocalField.nhdsNE_zero_neBot F

/-- The genuine rectangular product of the supplied scalar additive Haar measure
assigns measure zero to the singular locus, in every square size. -/
theorem rectangularMeasure_ae_det_ne_zero (ν : AdditiveHaarMeasure F) (r : ℕ) :
    ∀ᵐ X ∂rectangularMeasure ν r r, X.det ≠ 0 := by
  exact ae_det_ne_zero_of_addInvariant r ν.measure (rectangularMeasure ν r r)

/-- Restricting the supplied additive matrix Haar measure to the actual range
of the GL inclusion does not change that measure. -/
theorem rectangularMeasure_restrict_generalLinear (ν : AdditiveHaarMeasure F)
    (r : ℕ) :
    (rectangularMeasure ν r r).restrict
      (Set.range (Units.val : Langlands.GeneralLinear r F →
        Matrix (Fin r) (Fin r) F)) = rectangularMeasure ν r r := by
  apply Measure.restrict_eq_self_of_ae_mem
  filter_upwards [rectangularMeasure_ae_det_ne_zero F ν r] with X hX
  exact ((Matrix.isUnit_iff_isUnit_det X).mpr (isUnit_iff_ne_zero.mpr hX))

end CanonicalPadic

end Langlands.AllField.RankinSelberg.GLDeterminantDensity
