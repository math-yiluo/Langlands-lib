import Langlands.Representation.GodementJacquet.AnalyticData
import Langlands.AllField.Representation.GodementJacquet.Zeta
import Langlands.AllField.Representation.RankinSelberg.FunctionalEquationStatementSupplement
/-!
# Actual matrix analytic assertions and transpose Fourier data

These predicates record common shifted convergence, actual rational
continuations, normalized generators and the transpose Fourier functional
equation. They assert no existence theorem, including for reducible carriers.
-/

noncomputable section

namespace Langlands.AllField.GodementJacquet
open Langlands.GodementJacquet
open Langlands.AllField.GodementJacquet

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

universe uF uV

section TransformedCoefficients


end TransformedCoefficients

section MatrixAnalytics


end MatrixAnalytics

section FourierData



end FourierData

namespace Padic
open Langlands.GodementJacquet.Padic hiding IotaMatrixAnalyticAssertions IotaMatrixConvergesOnRight IsMatrixNormalizedGenerator MatrixAnalyticAssertions MatrixConverges MatrixConvergesOnRight MatrixFourierPair NormalizedMatrixFunctionalEquationData instBorelSpaceGeneralLinearHAddNatOfNatCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier_1 instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier_1 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instValuativeRelCarrier instValuativeRelCarrier_1 iotaMatrixRationalValues jpssI2 jpssI3 matrixIntegral matrixIntegrand matrixRationalValues whittakerRationalValues
open Langlands.AllField.GodementJacquet.Padic
open Langlands.GodementJacquet hiding IotaMatrixAnalyticAssertions IotaMatrixConvergesOnRight IsIotaMatrixNormalizedGenerator IsMatrixNormalizedGenerator MatrixAnalyticAssertions MatrixConverges MatrixConvergesOnRight MatrixFourierPair NormalizedMatrixFunctionalEquationData iotaMatrixRationalValues jpssI2 jpssI3 matrixIntegral matrixIntegrand matrixRationalValues whittakerRationalValues
open Langlands.AllField.GodementJacquet

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance : MeasurableSpace F := borel _
local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear (n + 1) F) :=
  borel _
local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩

variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Transformed values with the canonical p-adic normalizations of `Zeta`. -/
def iotaMatrixRationalValues
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V) :
    Set RationalFunctions :=
  GodementJacquet.iotaMatrixRationalValues (⟨⟩ : LocalFieldData F).residueCardinality
    (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) (generalLinearHaar F n) σ

/-- Common shifted convergence with canonical topology and normalized group Haar measure. -/
def MatrixConvergesOnRight
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V) : Prop :=
  GodementJacquet.MatrixConvergesOnRight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
    (generalLinearHaar F n) σ

/-- Common transformed shifted convergence with the same canonical group measure. -/
def IotaMatrixConvergesOnRight
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V) : Prop :=
  GodementJacquet.IotaMatrixConvergesOnRight
    (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) (generalLinearHaar F n) σ

/-- A proposed normalized generator for the canonical published matrix values. -/
def IsMatrixNormalizedGenerator
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (P : Polynomial ℂ) : Prop :=
  GodementJacquet.IsMatrixNormalizedGenerator (⟨⟩ : LocalFieldData F).residueCardinality
    (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) (generalLinearHaar F n) σ P

/-- Actual matrix analytic assertions with all canonical p-adic normalizations. -/
def MatrixAnalyticAssertions
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (P : Polynomial ℂ) : Prop :=
  GodementJacquet.MatrixAnalyticAssertions (⟨⟩ : LocalFieldData F).residueCardinality
    (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) (generalLinearHaar F n) σ P

/-- Transformed analytic assertions with the same canonical p-adic normalizations. -/
def IotaMatrixAnalyticAssertions
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (P : Polynomial ℂ) : Prop :=
  GodementJacquet.IotaMatrixAnalyticAssertions (⟨⟩ : LocalFieldData F).residueCardinality
    (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) (generalLinearHaar F n) σ P

/-- The actual plus transpose Fourier relation with canonical Borel structures.
The scalar additive measure is supplied, with no normalization change. -/
def MatrixFourierPair (ψ : UnitaryAdditiveCharacter F)
    (ν : AdditiveHaarMeasure F) (Φ ΦHat : MatrixTestFunction n F) : Prop :=
  GodementJacquet.MatrixFourierPair ψ ν Φ ΦHat

/-- Canonical p-adic functional-equation data retaining the supplied scalar
Fourier measure. Self-duality is a premise for later existence theorems. -/
def NormalizedMatrixFunctionalEquationData (ψ : UnitaryAdditiveCharacter F)
    (ν : AdditiveHaarMeasure F)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (P PDual : Polynomial ℂ) (c : ℂˣ) (m : ℤ) : Prop :=
  GodementJacquet.NormalizedMatrixFunctionalEquationData
    (⟨⟩ : LocalFieldData F).residueCardinality ψ ν
    (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) (generalLinearHaar F n)
    σ P PDual c m

end Padic

end Langlands.AllField.GodementJacquet
