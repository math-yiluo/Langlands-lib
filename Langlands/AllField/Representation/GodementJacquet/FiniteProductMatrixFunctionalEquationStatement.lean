import Langlands.Representation.GodementJacquet.FiniteProductMatrixFunctionalEquationStatement
import Langlands.AllField.Representation.GodementJacquet.AnalyticData
import Langlands.AllField.Representation.Induction.BlockFactors
/-! # Existence of normalized matrix data on a finite normalized product -/

noncomputable section

namespace Langlands.AllField.GodementJacquet
open Langlands.GodementJacquet hiding FiniteProductMatrixFunctionalEquationStatement
open Langlands.AllField.GodementJacquet

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis

universe uF uV

namespace Padic
open Langlands.GodementJacquet.Padic hiding HasNormalizedMatrixFunctionalEquationData IotaMatrixAnalyticAssertions IotaMatrixConvergesOnRight IsMatrixNormalizedGenerator MatrixAnalyticAssertions MatrixConverges MatrixConvergesOnRight MatrixFourierPair NormalizedMatrixFunctionalEquationData finiteProductMeasurable finiteProductTopology instBorelSpaceGeneralLinearHAddNatOfNatCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier_1 instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier_1 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instValuativeRelCarrier instValuativeRelCarrier_1 iotaMatrixRationalValues jpssI2 jpssI3 matrixIntegral matrixIntegrand matrixRationalValues whittakerRationalValues
open Langlands.AllField.GodementJacquet.Padic
open Langlands.GodementJacquet hiding FiniteProductMatrixFunctionalEquationStatement IotaMatrixAnalyticAssertions IotaMatrixConvergesOnRight IsIotaMatrixNormalizedGenerator IsMatrixNormalizedGenerator MatrixAnalyticAssertions MatrixConverges MatrixConvergesOnRight MatrixFourierPair NormalizedMatrixFunctionalEquationData iotaMatrixRationalValues jpssI2 jpssI3 matrixIntegral matrixIntegrand matrixRationalValues whittakerRationalValues
open Langlands.AllField.GodementJacquet

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance finiteProductMeasurable : MeasurableSpace F := borel _

/-- Existence of the unchanged normalized data, indexed by the actual rank.
Rank zero is excluded; at rank `n+1` the four normalization parameters are
existentially quantified on the supplied actual representation. -/
def HasNormalizedMatrixFunctionalEquationData
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    {r : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear r F) V) : Prop :=
  match r, σ with
  | 0, _ => False
  | _n + 1, σ => ∃ (P PDual : Polynomial ℂ) (c : ℂˣ) (a : ℤ),
      NormalizedMatrixFunctionalEquationData F ψ ν σ P PDual c a

end Padic

/-- A finite actual normalized product has normalized matrix data whenever its
smooth admissible block factors have those data and scalar central
quasicharacters. This is a conditional closure assertion, not an analytic base. -/
def FiniteProductMatrixFunctionalEquationStatement : Prop :=
  ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F],
    letI : MeasurableSpace F := borel _
    haveI : BorelSpace F := ⟨rfl⟩
    haveI : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
    haveI : TotallyDisconnectedSpace F := by
      let : NonarchimedeanRing F := by
        convert! ValuativeRel.nonarchimedeanRing F
        exact Valuation.toTopologicalSpace_eq _
      infer_instance
    ∀ (r : ℕ), 0 < r →
    ∀ (B : GeneralLinear.BlockShape r)
      (A : ∀ i, SmoothRep.{0,uF,uV} ℂ
        (Langlands.GeneralLinear (B.size i) F)),
      (∀ i, IsAdmissible (A i).representation) →
      ∀ (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F),
      IsSelfDual ψ ν →
      ∀ (ω : Fin B.length → Quasicharacter F),
      (∀ i, Classification.HasGLCentralCharacter F (B.size i)
        (A i).representation (ω i).toMonoidHom) →
      (∀ i, Langlands.AllField.GodementJacquet.Padic.HasNormalizedMatrixFunctionalEquationData F ψ ν
        (A i).representation) →
      Langlands.AllField.GodementJacquet.Padic.HasNormalizedMatrixFunctionalEquationData F ψ ν
        ((⟨⟩ : LocalFieldData F).normalizedProductInduced B (fun i => (A i).representation))

end Langlands.AllField.GodementJacquet
