import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonGLAdditive
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonFramedIntegrability
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonGLDensity
/-! # Cancelling determinant density for the actual GL Haar measure -/

noncomputable section

namespace Langlands.AllField.RankinSelberg.GLDeterminantDensity
open Langlands.RankinSelberg.GLDeterminantDensity hiding forwardWeight_eq_determinantWeight instBorelSpaceCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier instIsNonarchimedeanLocalFieldCarrier instLocallyCompactSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instSecondCountableTopologyCarrier instSecondCountableTopologyGeneralLinearHAddNatOfNatCarrier instSigmaCompactSpaceCarrier instT2SpaceCarrier instTopologicalSpaceCarrier instValuativeRelCarrier integrable_generalLinearHaar_natWeight_iff integrable_prod_generalLinearHaar_natWeight_iff integral_generalLinearHaar_natWeight integral_prod_generalLinearHaar_natWeight padic_exists_weightedRestriction_eq_generalLinearHaar padic_weightedRestriction_isHaar rectangularHaarScalar rectangularHaarScalar_pos weightedRestriction_eq_rectangularHaarScalar
open Langlands.AllField.RankinSelberg.GLDeterminantDensity
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement diagonalConj_map exists_rankOneCutoff exists_rankOneEmbedding_support lastRowCompactOrbit normalizedAbsoluteValue normalizedAbsoluteValue_apply rankOneModelValues_subset_whittakerRationalValues singleton_modulus_real zeroRowLastRowCutoff
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding PadicSelfDualMeasureExistsStatement padicLatticeGeometry padicRectangularHaarScaling padicScalarHaarScaling padicSelfDualMeasureExists
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding MirabolicUnitTestStatement mirabolicUnitTest
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear hiding padic_exists_ne_zero_mem_nhds_zero
open Langlands.AllField.GeneralLinear
open scoped NNReal ENNReal

universe uK uF uE uH

section Algebra


end Algebra

section General

variable {K : Type uK} [Field K] [TopologicalSpace K]
  [IsTopologicalDivisionRing K] [T2Space K] (r : ℕ) (χ : K →*₀ ℝ≥0)
  [MeasurableSpace (Matrix (Fin r) (Fin r) K)]
  [BorelSpace (Matrix (Fin r) (Fin r) K)]
  [MeasurableSpace (Langlands.GeneralLinear r K)]
  [BorelSpace (Langlands.GeneralLinear r K)]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

section Product


end Product

end General

section CanonicalPadic

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance : SecondCountableTopology F :=
  (⟨⟩ : LocalFieldData F).secondCountableTopology
local instance : SigmaCompactSpace F := (⟨⟩ : LocalFieldData F).sigmaCompactSpace
local instance : MeasurableSpace F := borel _
local instance : BorelSpace F := ⟨rfl⟩
local instance (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F) := borel _
local instance (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
local instance (n : ℕ) :
    LocallyCompactSpace (Langlands.GeneralLinear (n + 1) F) :=
  (⟨⟩ : LocalFieldData F).generalLinearLocallyCompactSpace (n + 1)
local instance (n : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear (n + 1) F) :=
  (⟨⟩ : LocalFieldData F).generalLinearSecondCountableTopology (n + 1)

local notation "abv" => normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)
local notation "χ" => (Langlands.LocalFieldData.normalizedAbsHom (⟨⟩ : LocalFieldData F))

/-- One fixed positive normalization scalar for the supplied scalar Haar
measure, used for every function and test. -/
def rectangularHaarScalar (ν : AdditiveHaarMeasure F) (n : ℕ) : ℝ≥0 :=
  (padic_exists_weightedRestriction_eq_generalLinearHaar
    F (⟨⟩ : LocalFieldData F) n (rectangularMeasure ν (n + 1) (n + 1))).choose

theorem rectangularHaarScalar_pos (ν : AdditiveHaarMeasure F) (n : ℕ) :
    0 < rectangularHaarScalar F ν n :=
  (padic_exists_weightedRestriction_eq_generalLinearHaar
    F (⟨⟩ : LocalFieldData F) n (rectangularMeasure ν (n + 1) (n + 1))).choose_spec.1

theorem weightedRestriction_eq_rectangularHaarScalar
    (ν : AdditiveHaarMeasure F) (n : ℕ) :
    weightedRestriction (n + 1) χ (rectangularMeasure ν (n + 1) (n + 1)) =
      rectangularHaarScalar F ν n • generalLinearHaar F n :=
  (padic_exists_weightedRestriction_eq_generalLinearHaar
    F (⟨⟩ : LocalFieldData F) n (rectangularMeasure ν (n + 1) (n + 1))).choose_spec.2

theorem forwardWeight_eq_determinantWeight (n : ℕ)
    (g : Langlands.GeneralLinear (n + 1) F) (z : ℂ) :
    forwardWeight (n + 1) χ g.val • z =
      determinantWeight abv g (n + 1 : ℕ) * z := by
  simp only [forwardWeight, NNReal.smul_def, Complex.real_smul,
    NNReal.coe_pow, Complex.ofReal_pow, determinantWeight, Complex.cpow_natCast]
  rfl

/-- The actual natural matrix-size determinant power converts GL convergence
to additive convergence on the invertible locus, with the same supplied ν. -/
theorem integrable_generalLinearHaar_natWeight_iff
    (ν : AdditiveHaarMeasure F) (n : ℕ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) F → ℂ) :
    Integrable (fun g : Langlands.GeneralLinear (n + 1) F =>
      determinantWeight abv g (n + 1 : ℕ) * A g.val)
      (generalLinearHaar F n) ↔
    Integrable A ((rectangularMeasure ν (n + 1) (n + 1)).restrict
      (Set.range (Units.val : Langlands.GeneralLinear (n + 1) F →
        Matrix (Fin (n + 1)) (Fin (n + 1)) F))) := by
  simpa only [forwardWeight_eq_determinantWeight F] using
    integrable_forwardWeight_iff_of_eq_smul (n + 1) χ
      (⟨⟩ : LocalFieldData F).continuous_normalizedAbsHom
      (rectangularMeasure ν (n + 1) (n + 1)) (generalLinearHaar F n)
      (rectangularHaarScalar F ν n) (rectangularHaarScalar_pos F ν n)
      (weightedRestriction_eq_rectangularHaarScalar F ν n) A

/-- The natural determinant power cancels the density; the one positive
normalization scalar is retained explicitly. -/
theorem integral_generalLinearHaar_natWeight
    (ν : AdditiveHaarMeasure F) (n : ℕ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) F → ℂ) :
    (∫ g : Langlands.GeneralLinear (n + 1) F,
      determinantWeight abv g (n + 1 : ℕ) * A g.val
        ∂generalLinearHaar F n) =
    ((rectangularHaarScalar F ν n : ℝ) : ℂ)⁻¹ *
      ∫ X, A X ∂(rectangularMeasure ν (n + 1) (n + 1)).restrict
        (Set.range (Units.val : Langlands.GeneralLinear (n + 1) F →
          Matrix (Fin (n + 1)) (Fin (n + 1)) F)) := by
  simpa only [forwardWeight_eq_determinantWeight F, NNReal.smul_def,
    NNReal.coe_inv, Complex.real_smul, Complex.ofReal_inv] using
    integral_forwardWeight_of_eq_smul (n + 1) χ
      (⟨⟩ : LocalFieldData F).continuous_normalizedAbsHom
      (rectangularMeasure ν (n + 1) (n + 1)) (generalLinearHaar F n)
      (rectangularHaarScalar F ν n) (rectangularHaarScalar_pos F ν n)
      (weightedRestriction_eq_rectangularHaarScalar F ν n) A

/-- Product-measure convergence for the canonical GL measure and supplied ν. -/
theorem integrable_prod_generalLinearHaar_natWeight_iff
    {H : Type uH} [MeasurableSpace H] (μH : Measure H) [SFinite μH]
    (ν : AdditiveHaarMeasure F) (n : ℕ)
    (A : H × Matrix (Fin (n + 1)) (Fin (n + 1)) F → ℂ) :
    Integrable (fun z : H × Langlands.GeneralLinear (n + 1) F =>
      determinantWeight abv z.2 (n + 1 : ℕ) * A (z.1, z.2.val))
        (μH.prod (generalLinearHaar F n)) ↔
    Integrable A (μH.prod ((rectangularMeasure ν (n + 1) (n + 1)).restrict
      (Set.range (Units.val : Langlands.GeneralLinear (n + 1) F →
        Matrix (Fin (n + 1)) (Fin (n + 1)) F)))) := by
  simpa only [forwardWeight_eq_determinantWeight F] using
    integrable_prod_forwardWeight_iff_of_eq_smul (n + 1) χ
      (⟨⟩ : LocalFieldData F).continuous_normalizedAbsHom μH
      (rectangularMeasure ν (n + 1) (n + 1)) (generalLinearHaar F n)
      (rectangularHaarScalar F ν n) (rectangularHaarScalar_pos F ν n)
      (weightedRestriction_eq_rectangularHaarScalar F ν n) A

/-- The product integral retains the same positive scalar as the single GL
integral, independently of the auxiliary measure and the integrand. -/
theorem integral_prod_generalLinearHaar_natWeight
    {H : Type uH} [MeasurableSpace H] (μH : Measure H) [SFinite μH]
    (ν : AdditiveHaarMeasure F) (n : ℕ)
    (A : H × Matrix (Fin (n + 1)) (Fin (n + 1)) F → ℂ) :
    (∫ z : H × Langlands.GeneralLinear (n + 1) F,
      determinantWeight abv z.2 (n + 1 : ℕ) * A (z.1, z.2.val)
        ∂μH.prod (generalLinearHaar F n)) =
    ((rectangularHaarScalar F ν n : ℝ) : ℂ)⁻¹ *
      ∫ z, A z ∂μH.prod ((rectangularMeasure ν (n + 1) (n + 1)).restrict
        (Set.range (Units.val : Langlands.GeneralLinear (n + 1) F →
          Matrix (Fin (n + 1)) (Fin (n + 1)) F))) := by
  simpa only [forwardWeight_eq_determinantWeight F, NNReal.smul_def,
    NNReal.coe_inv, Complex.real_smul, Complex.ofReal_inv] using
    integral_prod_forwardWeight_of_eq_smul (n + 1) χ
      (⟨⟩ : LocalFieldData F).continuous_normalizedAbsHom μH
      (rectangularMeasure ν (n + 1) (n + 1)) (generalLinearHaar F n)
      (rectangularHaarScalar F ν n) (rectangularHaarScalar_pos F ν n)
      (weightedRestriction_eq_rectangularHaarScalar F ν n) A

end CanonicalPadic

end Langlands.AllField.RankinSelberg.GLDeterminantDensity
