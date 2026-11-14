import Langlands.Representation.GodementJacquet.SubquotientFunctionalEquationDescent
import Langlands.AllField.Representation.GodementJacquet.MatrixUnitValueProof
import Langlands.AllField.Representation.GodementJacquet.SubquotientCoefficientInclusionProof
import Langlands.AllField.Representation.RankinSelberg.GammaFactor
import Langlands.AllField.Representation.RankinSelberg.PairLFactor
/-! # Normalized matrix equation data on actual p-adic subquotients -/

noncomputable section

namespace Langlands.AllField.GodementJacquet.Padic
open Langlands.GodementJacquet.Padic hiding IotaMatrixAnalyticAssertions IotaMatrixConvergesOnRight IsMatrixNormalizedGenerator MatrixAnalyticAssertions MatrixConverges MatrixConvergesOnRight MatrixFourierPair NormalizedMatrixFunctionalEquationData SubquotientCoefficientInclusionStatement exists_biSmoothCoefficient_ne_zero exists_matrixIntegral_one instBorelSpaceGeneralLinearHAddNatOfNatCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier_1 instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier_1 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instValuativeRelCarrier instValuativeRelCarrier_1 iotaMatrixRationalValues jpssI2 jpssI3 matrixIntegral matrixIntegrand matrixRationalValues matrixUnitValueGLBorel matrixUnitValueGLMeasurable matrixUnitValueLocalField matrixUnitValueT2 matrixUnitValueTopology matrixUnitValueValuation normalizedMatrixFunctionalEquationData_of_coefficient_inclusion normalizedMatrixFunctionalEquationData_of_subquotient one_mem_iotaMatrixRationalValues one_mem_matrixRationalValues subquotientCoefficientInclusion subquotientDescentBorelSpace subquotientDescentGLBorelSpace subquotientDescentGLMeasurableSpace subquotientDescentLocalField subquotientDescentMeasurableSpace subquotientDescentT2Space subquotientDescentTopology subquotientDescentTotallyDisconnectedSpace subquotientDescentValuativeRel whittakerRationalValues
open Langlands.AllField.GodementJacquet.Padic
open Langlands.GodementJacquet hiding IotaMatrixAnalyticAssertions IotaMatrixConvergesOnRight IsIotaMatrixNormalizedGenerator IsMatrixNormalizedGenerator MatrixAnalyticAssertions MatrixConverges MatrixConvergesOnRight MatrixFourierPair MatrixUnitValueStatement NormalizedMatrixFunctionalEquationData SubquotientCoefficientInclusionStatement iotaMatrixRationalValues jpssI2 jpssI3 matrixIntegral matrixIntegrand matrixRationalValues matrixUnitValue subquotientCoefficientInclusion whittakerRationalValues
open Langlands.AllField.GodementJacquet

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement IsPadicPairGammaFactor LastRowCompactOrbitStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement lastRowCompactOrbit normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

universe uF uV uW

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance subquotientDescentT2Space : T2Space F :=
  (⟨⟩ : LocalFieldData F).fieldT2
local instance subquotientDescentTotallyDisconnectedSpace :
    TotallyDisconnectedSpace F := by
  let : NonarchimedeanRing F := by
    convert! ValuativeRel.nonarchimedeanRing F
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance subquotientDescentMeasurableSpace : MeasurableSpace F := borel _
local instance subquotientDescentBorelSpace : BorelSpace F := ⟨rfl⟩
local instance subquotientDescentGLMeasurableSpace (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F) :=
  borel _
local instance subquotientDescentGLBorelSpace (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩

variable {n : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W] [Nontrivial W]
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V}
  {τ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}

/-- A nonzero smooth coefficient subfamily inherits full normalized matrix data,
with new generators, unit and exponent. -/
theorem normalizedMatrixFunctionalEquationData_of_coefficient_inclusion
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (hsd : IsSelfDual ψ ν) (hτ : IsSmooth τ)
    (hincl : biSmoothMatrixCoefficients τ ≤ biSmoothMatrixCoefficients σ)
    {P PDual : Polynomial ℂ} {c : ℂˣ} {m : ℤ}
    (hdata : NormalizedMatrixFunctionalEquationData F ψ ν σ P PDual c m) :
    ∃ (Q QDual : Polynomial ℂ) (d : ℂˣ) (a : ℤ),
      NormalizedMatrixFunctionalEquationData F ψ ν τ Q QDual d a := by
  obtain ⟨hone, honeDual⟩ := matrixUnitValue F n W τ hτ
  exact GodementJacquet.normalizedMatrixFunctionalEquationDescent
    F n V W (⟨⟩ : LocalFieldData F).residueCardinality ψ ν
    (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) (generalLinearHaar F n)
    σ τ (⟨⟩ : LocalFieldData F).residueCardinality_gt_one hsd hincl
    (mem_zetaSpan hone) (mem_zetaSpan honeDual) P PDual c m hdata

/-- Every nonzero actual subquotient of a smooth representation inherits its
full normalized matrix equation data for the supplied self-dual Fourier measure. -/
theorem normalizedMatrixFunctionalEquationData_of_subquotient
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (hsd : IsSelfDual ψ ν) (hσ : IsSmooth σ)
    (A : Subrepresentation σ) (f : A.toRepresentation.IntertwiningMap τ)
    (hf : Function.Surjective f)
    {P PDual : Polynomial ℂ} {c : ℂˣ} {m : ℤ}
    (hdata : NormalizedMatrixFunctionalEquationData F ψ ν σ P PDual c m) :
    ∃ (Q QDual : Polynomial ℂ) (d : ℂˣ) (a : ℤ),
      NormalizedMatrixFunctionalEquationData F ψ ν τ Q QDual d a := by
  let i : A.toRepresentation.IntertwiningMap σ :=
    { toLinearMap := A.toSubmodule.subtype
      isIntertwining' _ := by ext; rfl }
  have hA : IsSmooth A.toRepresentation :=
    isSmooth_of_injective i Subtype.val_injective hσ
  have hτ : IsSmooth τ := isSmooth_of_surjective f hf hA
  exact normalizedMatrixFunctionalEquationData_of_coefficient_inclusion F ψ ν hsd hτ
    (subquotientCoefficientInclusion F n V W σ τ hσ A f hf) hdata

end Langlands.AllField.GodementJacquet.Padic
