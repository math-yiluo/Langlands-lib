import Langlands.Representation.RankinSelberg.AdjacentRankIntegralModel
import Langlands.AllField.HarmonicAnalysis.MatrixFourierSliceProof
import Langlands.AllField.Representation.RankinSelberg.AnalyticStatementSupplement
/-!
# JPSS Section 6.1: the special `(r+1,1)` tensor integral model

The raw scalar integral of JPSS Section 6.1, formula (8), in ambient rank `r + 2`
with lower blocks `(r + 1, 1)`. Test vectors are finite tensors of rectangular
Schwartz functions with vectors of the actual Whittaker coefficient image, and
`ρ₀` acts on the Schwartz factor only. The integral is the totalized Bochner
integral for a supplied measure; no convergence or model membership is asserted.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory TensorProduct
open Langlands.HarmonicAnalysis hiding PadicMatrixFourierSliceStatement PadicRowFourierSurjectivityStatement padicMatrixFourierSlice padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker

universe uF uV

section TestSpace


end TestSpace

section Kernel

open Matrix


end Kernel

section Action


end Action

section Integral



end Integral

section IntegralLaws



end IntegralLaws

/-! ## Canonical p-adic specializations

For `F : PadicField p` we use its canonical topology, the Borel structures, the
normalized absolute value and the shared Haar measure `generalLinearHaar F r`
on the inner `GL_(r+1)`, giving `GL_(r+1)(O_F)` mass one. The character `ψ`, the
scalar Haar measure `ν`, its self-duality, `σ`, `ℓ` and `χ` remain supplied. -/

namespace Padic
open Langlands.RankinSelberg.Padic hiding AdjacentRankModelConverges adjacentRankModelIntegral instBorelSpaceCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier instIsNonarchimedeanLocalFieldCarrier instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instT2SpaceCarrier instTopologicalSpaceCarrier instTotallyDisconnectedSpaceCarrier instValuativeRelCarrier
open Langlands.AllField.RankinSelberg.Padic
open Langlands.RankinSelberg hiding AdjacentRankModelConverges EqualRankAnalyticStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement adjacentRankModelIntegral adjacentRankModelIntegrand normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance : TotallyDisconnectedSpace F := by
  let : NonarchimedeanRing F := by
    convert! ValuativeRel.nonarchimedeanRing F
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance : MeasurableSpace F := borel _
local instance : BorelSpace F := ⟨rfl⟩
local instance (n : ℕ) : MeasurableSpace (GeneralLinear (n + 1) F) := borel _
local instance (n : ℕ) : BorelSpace (GeneralLinear (n + 1) F) := ⟨rfl⟩

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
  (hself : IsSelfDual ψ ν) {r : ℕ}
  (σ : Representation ℂ (GeneralLinear (r + 1) F) V) (ℓ : glFunctionals ψ r σ)
  (χ : Quasicharacter F)

/-- Convergence for the shared Haar measure on the inner `GL_(r+1)`. -/
def AdjacentRankModelConverges (Ψ : adjacentRankTestSpace ψ σ ℓ)
    (g : GeneralLinear (r + 2) F) : Prop :=
  RankinSelberg.AdjacentRankModelConverges ψ ν hself σ ℓ
    (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) χ (generalLinearHaar F r) Ψ g

/-- The raw formula (8) integral for the shared Haar measure on the inner `GL_(r+1)`. -/
def adjacentRankModelIntegral (Ψ : adjacentRankTestSpace ψ σ ℓ)
    (g : GeneralLinear (r + 2) F) : ℂ :=
  RankinSelberg.adjacentRankModelIntegral ψ ν hself σ ℓ
    (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) χ (generalLinearHaar F r) Ψ g

end Padic

end Langlands.AllField.RankinSelberg
