import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonPositiveAssembly
import Langlands.AllField.LocalFactor.ResidueReflection
import Langlands.AllField.Representation.GodementJacquet.AnalyticData
import Langlands.AllField.Representation.RankinSelberg.EqualRankCharacterChange
import Langlands.AllField.Representation.RankinSelberg.GammaFromWhittakerType
import Langlands.AllField.Representation.RankinSelberg.RankOneCharacterReductionProof
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonModels
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonZero
import Langlands.AllField.Representation.RankinSelberg.RankOneWhittakerTypeProof
import Langlands.AllField.Representation.RankinSelberg.UnequalRankBilinearUniquenessStatement
import Langlands.AllField.Representation.RankinSelberg.UnequalRankGammaPropagationProof
import Langlands.AllField.Representation.RankinSelberg.UnequalRankUnitSpanProof
import Langlands.AllField.Representation.RankinSelberg.ZeroRowLastRowCutoffProofSupplement
import Langlands.AllField.Representation.Whittaker.MirabolicUnitTestProof
/-!
# Assembly from a single-vector block-zero equation

The actual constant second model vector can be absorbed into the first vector,
simultaneously in the original and Weyl-transformed complementary integrals.
The analytic block-zero equation remains an explicit input.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LastRowCompactOrbitStatement PadicPairGammaConstructionInput PadicPairGammaInput PadicSymmetricGammaConstructionInput PadicSymmetricGammaInput QuotientHaarExistenceStatement RankOneCharacterReductionStatement RankOneMatrixWhittakerComparisonStatement RankOneWhittakerTypeStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement diagonal_abs_bound diagonal_abs_last glCoefficientModel_isOfWhittakerType isEqualRankLPolynomial_characterChange_normalized isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt lastRowCompactOrbit matrixComparisonModelsTopology matrixComparisonPositiveBorel matrixComparisonPositiveDisconnected matrixComparisonPositiveGLBorel matrixComparisonPositiveGLMeasurable matrixComparisonPositiveLocalField matrixComparisonPositiveMeasurable matrixComparisonPositiveQuotientBorel matrixComparisonPositiveQuotientMeasurable matrixComparisonPositiveT2 matrixComparisonPositiveTopology matrixComparisonPositiveUnipotentBorel matrixComparisonPositiveUnipotentMeasurable matrixComparisonPositiveValuation normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow padicPairGammaConstructionInput_iff padicPairGammaFactor padicPairGammaFactorOfWhittakerType padicSymmetricGammaConstructionInput_iff padicSymmetricGammaFactor padicSymmetricGammaFactorOfWhittakerType rankOneCharacterReduction rankOneCharacter_isOfWhittakerType rankOneGammaFactor_of_blockZero_one rankOneGammaFactor_of_normalized_blockZero_one rankOneMatrixWhittakerComparison_zero rankOneWhittakerType rankOne_blockZero_exists_ne_zero unequalRankCompactSupport unequalRankFiniteExpansion unequalRankGammaPropagation unequalRankIwasawaSupport unequalRankUnitSpan zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding PadicRowFourierSurjectivityStatement PadicSelfDualMeasureExistsStatement padicLatticeGeometry padicRowFourierSurjectivity padicScalarHaarScaling padicSelfDualMeasureExists
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding MirabolicUnitTestStatement mirabolicUnitTest modelKirillovTransfer smoothSimpleRootSupport
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
open Langlands.QuotientIntegration

universe uF uV

section Algebra




end Algebra

private theorem exists_ne_zero_of_one_mem_zetaSpan {S : Set RationalFunctions}
    (h : (1 : RationalFunctions) ∈ zetaSpan S) : ∃ R ∈ S, R ≠ 0 := by
  by_contra! hzero
  have hbot : zetaSpan S = ⊥ := (Submodule.span_eq_bot).mpr hzero
  rw [hbot, Submodule.mem_bot] at h
  exact one_ne_zero h

section Padic

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance matrixComparisonPositiveMeasurable : MeasurableSpace F := borel _
local instance matrixComparisonPositiveBorel : BorelSpace F := ⟨rfl⟩
local instance matrixComparisonPositiveT2 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance matrixComparisonPositiveDisconnected : TotallyDisconnectedSpace F := by
  let : NonarchimedeanRing F := by
    convert! ValuativeRel.nonarchimedeanRing F
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance matrixComparisonPositiveGLMeasurable : MeasurableSpace (Langlands.GeneralLinear (0 + 1) F) := borel _
local instance matrixComparisonPositiveGLBorel : BorelSpace (Langlands.GeneralLinear (0 + 1) F) := ⟨rfl⟩
local instance matrixComparisonPositiveUnipotentMeasurable : MeasurableSpace (upperUnipotent (0 + 1) F) := borel _
local instance matrixComparisonPositiveUnipotentBorel : BorelSpace (upperUnipotent (0 + 1) F) := ⟨rfl⟩
local instance matrixComparisonPositiveQuotientMeasurable : MeasurableSpace (LeftUnipotentQuotient 0 F) := borel _
local instance matrixComparisonPositiveQuotientBorel : BorelSpace (LeftUnipotentQuotient 0 F) := ⟨rfl⟩

variable {r : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
  (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
  (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
  (ℓ : glFunctionals ψ r π) (hℓ : ℓ.val ≠ 0)

include hπ hℓ in
/-- Unit membership for actual unequal-rank integrals supplies a nonzero
block-zero continuation for the supplied first model and canonical second model. -/
theorem rankOne_blockZero_exists_ne_zero (k : ℕ) (hr : r = 0 + (0 + k + 1)) :
    ∃ R ∈ unequalRankValuesAt 0 k hr
      (⟨⟩ : LocalFieldData F).residueCardinality ψ
      (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
      (unipotentQuotientHaar F 0) (rectangularMeasure ν 0 (0 + 1)) π
      (rankOneCharacter (1 : Fˣ →* ℂˣ)) ℓ (rankOneTrivialInverseFunctional ψ),
      R ≠ 0 := by
  subst r
  have htriv : IsOfWhittakerType 0 (inverseStandardCharacter ψ 0)
      (rankOneCharacter (1 : Fˣ →* ℂˣ)) := by
    apply (isOfWhittakerType_standard_iff_inverse ψ _).mp
    apply scalar_isOfWhittakerType_rankOne
    intro z
    refine ⟨⊤, fun g => ?_⟩
    simp [rankOneCharacter, characterRepresentation, twist]
  let := unipotentHaar_isMulRightInvariant F 0
  apply exists_ne_zero_of_one_mem_zetaSpan
  exact unequalRankUnitSpan.{uF, uV, 0} F (⟨⟩ : LocalFieldData F) 0 0 k
      ψ (unipotentQuotientHaar F 0)
      (unipotentQuotientHaar_isCompatible F 0) ν V ℂ π
      (rankOneCharacter (1 : Fˣ →* ℂˣ)) hπ htriv ℓ
      (rankOneTrivialInverseFunctional ψ) hℓ (rankOneTrivialInverseFunctional_ne_zero ψ)

include hπ hℓ in
/-- A block-zero equation for the canonical second vector supplies the full
symmetric gamma relation, with the same multiplier, all blocks, all compatible
quotient measures and all pairs of nonzero Whittaker functionals. -/
theorem rankOneGammaFactor_of_blockZero_one (hrpos : 0 < r) (hν : IsSelfDual ψ ν)
    {G : RationalFunctions}
    (hEquation : ∀ f : (coefficientModel π ℓ).toSubmodule,
      ∃ R Rd : RationalFunctions,
        HasRationalContinuation (⟨⟩ : LocalFieldData F).residueCardinality
          (unequalRankIntegralAt 0 (r - 0 - 1) (by omega) ψ
            (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
            (unipotentQuotientHaar F 0) (rectangularMeasure ν 0 (0 + 1))
            f.val (rankOneTrivialModelOne ψ).val) R ∧
        HasRationalContinuation (⟨⟩ : LocalFieldData F).residueCardinality
          (dualUnequalRankModelIntegralAt hrpos 0 (r - 0 - 1) (by omega) ψ
            (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
            (unipotentQuotientHaar F 0) ν π
            (rankOneCharacter (1 : Fˣ →* ℂˣ)) ℓ (rankOneTrivialInverseFunctional ψ)
            f (rankOneTrivialModelOne ψ)) Rd ∧
        GammaFunctionalEquation (⟨⟩ : LocalFieldData F).residueCardinality 1 r G R Rd) :
    IsPadicSymmetricGammaFactor F ψ ν π
      (rankOneCharacter (1 : Fˣ →* ℂˣ)) G := by
  have htriv : IsOfWhittakerType 0 (inverseStandardCharacter ψ 0)
      (rankOneCharacter (1 : Fˣ →* ℂˣ)) := by
    apply (isOfWhittakerType_standard_iff_inverse ψ _).mp
    apply scalar_isOfWhittakerType_rankOne
    intro z
    refine ⟨⊤, fun g => ?_⟩
    simp [rankOneCharacter, characterRepresentation, twist]
  let := unipotentHaar_isMulRightInvariant F 0
  have hNonzero := rankOne_blockZero_exists_ne_zero F ψ ν π hπ ℓ hℓ
    (r - 0 - 1) (by omega)
  have hZero := unequalRankBlockZeroGammaEquation_rankOne_of_one ψ
    (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
    (unipotentQuotientHaar F 0) ν π ℓ hrpos hNonzero hEquation
  have hFE := unequalRankGammaPropagation.{uF, uV, 0} F (⟨⟩ : LocalFieldData F) 0 r
    hrpos ψ (unipotentQuotientHaar F 0)
    (unipotentQuotientHaar_isCompatible F 0) ν hν V ℂ π
    (rankOneCharacter (1 : Fˣ →* ℂˣ)) hπ htriv ℓ
    (rankOneTrivialInverseFunctional ψ) hℓ (rankOneTrivialInverseFunctional_ne_zero ψ)
    G hZero
  have hFactor := unequalRankGammaFactor_of_equation hrpos hπ htriv hℓ
    (rankOneTrivialInverseFunctional_ne_zero ψ) hFE
  simpa only [IsPadicSymmetricGammaFactor, Nat.zero_le, ite_true,
    IsPadicPairGammaFactor, isPairGammaFactor_of_lt hrpos] using hFactor

include hπ hℓ in
/-- The normalized equation for the same actual block-zero pair yields the
specified rational gamma expression on its full reduced-denominator domain. -/
theorem rankOneGammaFactor_of_normalized_blockZero_one (hrpos : 0 < r)
    (hν : IsSelfDual ψ ν) {P PDual : Polynomial ℂ} {c : ℂˣ} {a : ℤ}
    (hPDual : PDual ≠ 0)
    (hEquation : ∀ f : (coefficientModel π ℓ).toSubmodule,
      ∃ R Rd : RationalFunctions,
        HasRationalContinuation (⟨⟩ : LocalFieldData F).residueCardinality
          (unequalRankIntegralAt 0 (r - 0 - 1) (by omega) ψ
            (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
            (unipotentQuotientHaar F 0) (rectangularMeasure ν 0 (0 + 1))
            f.val (rankOneTrivialModelOne ψ).val) R ∧
        HasRationalContinuation (⟨⟩ : LocalFieldData F).residueCardinality
          (dualUnequalRankModelIntegralAt hrpos 0 (r - 0 - 1) (by omega) ψ
            (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
            (unipotentQuotientHaar F 0) ν π
            (rankOneCharacter (1 : Fˣ →* ℂˣ)) ℓ (rankOneTrivialInverseFunctional ψ)
            f (rankOneTrivialModelOne ψ)) Rd ∧
        NormalizedFunctionalEquation (⟨⟩ : LocalFieldData F).residueCardinality
          P PDual 1 c 0 a R Rd) :
    IsPadicSymmetricGammaFactor F ψ ν π
      (rankOneCharacter (1 : Fˣ →* ℂˣ))
      (rationalGammaExpression (Langlands.AllField.LocalFactor.residueReflection F) c a P PDual) := by
  apply rankOneGammaFactor_of_blockZero_one F ψ ν π hπ ℓ hℓ hrpos hν
  intro f
  obtain ⟨R, Rd, hR, hRd, hN⟩ := hEquation f
  refine ⟨R, Rd, hR, hRd, ?_⟩
  intro s hs hsd hsg
  simpa only [Units.val_one, one_pow, one_mul] using
    hN.gamma_value_of_regular (⟨⟩ : LocalFieldData F).residueCardinality_gt_one
      (Langlands.AllField.LocalFactor.coe_residueReflection F) hPDual s hs hsd hsg

end Padic

end Langlands.AllField.RankinSelberg
