import Langlands.Representation.RankinSelberg.RankOneAmbientMatrixFunctionalEquationComparisonZeroPadic
import Langlands.AllField.Representation.RankinSelberg.EqualRankUnitValueProof
import Langlands.AllField.Representation.RankinSelberg.RankOneAmbientMatrixFunctionalEquationComparisonStatement
import Langlands.AllField.Representation.RankinSelberg.RankOneCharacterReductionProof
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonModels
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonZero
import Langlands.AllField.Representation.RankinSelberg.RankOneWhittakerTypeProof
/-!
# The rank-zero ambient matrix-to-gamma comparison

Ambient coefficients supply the equations and continuations. An independent
compact model test supplies rational value one, without using either ambient
normalized generator as a model generator.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement EqualRankUnitValueStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LastRowCompactOrbitStatement QuotientHaarExistenceStatement RankOneAmbientMatrixFunctionalEquationComparisonStatement RankOneCharacterReductionStatement RankOneMatrixWhittakerComparisonStatement RankOneWhittakerTypeStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement ambientZeroGLBorel ambientZeroGLMeasurable ambientZeroLocalField ambientZeroQuotientBorel ambientZeroQuotientMeasurable ambientZeroScalarMeasurable ambientZeroTopology ambientZeroUnipotentBorel ambientZeroUnipotentMeasurable ambientZeroValuation equalRankUnitValue glCoefficientModel_isOfWhittakerType hasEqualRankCompactTest_of_kirillov isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt lastRowCompactOrbit matrixComparisonModelsTopology normalizedAbsoluteValue normalizedAbsoluteValue_apply rankOneAmbientMatrixFunctionalEquationComparison_zero rankOneAmbientModelMatrixCoefficient rankOneCharacterReduction rankOneCharacter_isOfWhittakerType rankOneMatrixWhittakerComparison_zero rankOneWhittakerType zeroRowLastRowCutoff
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding MirabolicUnitTestStatement exists_compactOpen_glCoefficientRightStabilizer mirabolicUnitTest modelKirillovTransfer
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
open Langlands.QuotientIntegration

universe uF uV uW

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance ambientZeroScalarMeasurable : MeasurableSpace F := borel _
local instance ambientZeroGLMeasurable :
    MeasurableSpace (Langlands.GeneralLinear (0 + 1) F) := borel _
local instance ambientZeroGLBorel :
    BorelSpace (Langlands.GeneralLinear (0 + 1) F) := ⟨rfl⟩
local instance ambientZeroUnipotentMeasurable :
    MeasurableSpace (upperUnipotent (0 + 1) F) := borel _
local instance ambientZeroUnipotentBorel :
    BorelSpace (upperUnipotent (0 + 1) F) := ⟨rfl⟩
local instance ambientZeroQuotientMeasurable :
    MeasurableSpace (LeftUnipotentQuotient 0 F) := borel _
local instance ambientZeroQuotientBorel :
    BorelSpace (LeftUnipotentQuotient 0 F) := ⟨rfl⟩

/-- The actual rank-one model coefficient, with its constant second vector
absorbed, as a bi-smooth coefficient of the specified ambient representation. -/
def rankOneAmbientModelMatrixCoefficient
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ψ : UnitaryAdditiveCharacter F)
    (σ : Representation ℂ (Langlands.GeneralLinear (0 + 1) F) V)
    (hσ : IsOfWhittakerType 0 (standardCharacter ψ 0) σ)
    (ℓ : glFunctionals ψ 0 σ) (hℓ : ℓ.val ≠ 0)
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Langlands.GeneralLinear (0 + 1) F) W)
    (hinc : GodementJacquet.biSmoothMatrixCoefficients
        (V := (glCoefficientModel ψ 0 σ ℓ).toSubmodule)
        (glModelRepresentation ψ 0 σ ℓ) ≤
      GodementJacquet.biSmoothMatrixCoefficients ρ)
    (ℓ' : glInverseFunctionals ψ 0 (rankOneCharacter (1 : Fˣ →* ℂˣ)))
    (f : (coefficientModel σ ℓ).toSubmodule)
    (f' : (coefficientModel (rankOneCharacter (1 : Fˣ →* ℂˣ)) ℓ').toSubmodule) :
    GodementJacquet.biSmoothMatrixCoefficients ρ :=
  ⟨(rankOneModelMatrixCoefficient ψ σ hσ ℓ hℓ ℓ' f f').val,
    hinc (rankOneModelMatrixCoefficient ψ σ hσ ℓ hℓ ℓ' f f').property⟩

/-- Full ambient matrix data imply the rank-one symmetric gamma certificate
for the original representation. The model has its own compact unit test;
no ambient normalized-generator witness is restricted to the model. -/
theorem rankOneAmbientMatrixFunctionalEquationComparison_zero
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (σ : Representation ℂ (Langlands.GeneralLinear (0 + 1) F) V)
    (hσ : IsOfWhittakerType 0 (standardCharacter ψ 0) σ)
    (ℓ : glFunctionals ψ 0 σ) (hℓ : ℓ.val ≠ 0)
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Langlands.GeneralLinear (0 + 1) F) W)
    (hinc : GodementJacquet.biSmoothMatrixCoefficients
        (V := (glCoefficientModel ψ 0 σ ℓ).toSubmodule)
        (glModelRepresentation ψ 0 σ ℓ) ≤
      GodementJacquet.biSmoothMatrixCoefficients ρ)
    {P PDual : Polynomial ℂ} {c : ℂˣ} {a : ℤ}
    (hdata : Langlands.AllField.GodementJacquet.Padic.NormalizedMatrixFunctionalEquationData F ψ ν
      ρ P PDual c a) :
    IsPadicSymmetricGammaFactor F ψ ν σ
      (rankOneCharacter (1 : Fˣ →* ℂˣ))
      (rationalGammaExpression (Langlands.AllField.LocalFactor.residueReflection F) c a P PDual) := by
  have htriv : IsOfWhittakerType 0 (inverseStandardCharacter ψ 0)
      (rankOneCharacter (1 : Fˣ →* ℂˣ)) := by
    apply (isOfWhittakerType_standard_iff_inverse ψ _).mp
    apply scalar_isOfWhittakerType_rankOne
    intro z
    refine ⟨⊤, fun g => ?_⟩
    simp [rankOneCharacter, characterRepresentation, twist]
  let ℓ' := rankOneTrivialInverseFunctional ψ
  have hℓ' : ℓ'.val ≠ 0 := rankOneTrivialInverseFunctional_ne_zero ψ
  have hFE : EqualRankGammaEquation (⟨⟩ : LocalFieldData F).residueCardinality ψ
      (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
      (rankOneQuotientHaar F) ν
      σ (rankOneCharacter (1 : Fˣ →* ℂˣ)) ℓ ℓ'
      (rationalGammaExpression (Langlands.AllField.LocalFactor.residueReflection F) c a P PDual) := by
    refine ⟨1, rankOneTrivialModel_minusOne ψ ℓ', ?_, ?_⟩
    · have hone := equalRankUnitValue.{uF, uV, 0} F (⟨⟩ : LocalFieldData F) 0 ψ
        (rankOneQuotientHaar F) (rankOneQuotientHaar_isCompatible F)
        V ℂ σ (rankOneCharacter (1 : Fˣ →* ℂˣ)) hσ htriv ℓ ℓ' hℓ hℓ'
      exact ⟨1, hone, one_ne_zero⟩
    · intro f f' Φ
      let Φmat := schwartzBruhatComap (oneByOneRow F) Φ
      obtain ⟨ΦmatHat, hFourier, hmatrixFE⟩ := hdata.2.2 Φmat
      let Φhat := schwartzBruhatComap (oneByOneRow F).symm ΦmatHat
      have htest : schwartzBruhatComap (oneByOneRow F) Φhat = ΦmatHat := by
        exact (oneByOneSchwartzEquiv (F := F)).apply_symm_apply ΦmatHat
      have hrow : IsRowFourierPair ψ ν Φ Φhat := by
        intro y
        change ΦmatHat ((oneByOneRow F).symm y) = _
        have hy := (hFourier ((oneByOneRow F).symm y)).2
        change ΦmatHat ((oneByOneRow F).symm y) =
          rectangularFourierIntegral ψ ν (fun x => Φ (oneByOneRow F x))
            ((oneByOneRow F).symm y) at hy
        simpa only [rectangularFourierIntegral_oneByOneRow,
          Homeomorph.apply_symm_apply] using hy
      let fc := rankOneAmbientModelMatrixCoefficient F ψ σ hσ ℓ hℓ ρ hinc ℓ' f f'
      obtain ⟨R, hR⟩ := hdata.1.2.1 Φmat fc
      obtain ⟨RDual, hRDual⟩ := hdata.2.1.2.1 ΦmatHat fc
      have hN := hmatrixFE fc R RDual hR hRDual
      refine ⟨Φhat, R, RDual, hrow, ?_, ?_, ?_⟩
      · convert hR.2 using 1
        funext s
        exact equalRankModelIntegral_rankOne_eq_matrixIntegral ψ
          (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) σ ℓ ℓ' f f' Φ s
      · convert hRDual.2 using 1
        funext s
        rw [dualEqualRankModelIntegral_rankOne_eq_matrixIntegral, htest]
        rfl
      · intro s hR hRDual hG
        exact hN.gamma_value_of_regular (⟨⟩ : LocalFieldData F).residueCardinality_gt_one
          (Langlands.AllField.LocalFactor.coe_residueReflection F) hdata.2.1.2.2.polynomial_ne_zero
          s hR hRDual hG
  rw [← unipotentQuotientHaar_zero F] at hFE
  have hfactor := equalRankGammaFactor_of_equation hσ htriv hℓ hℓ' hFE
  simpa only [IsPadicSymmetricGammaFactor, Nat.le_refl, ite_true,
    IsPadicPairGammaFactor, isPairGammaFactor_self] using hfactor

end Langlands.AllField.RankinSelberg
