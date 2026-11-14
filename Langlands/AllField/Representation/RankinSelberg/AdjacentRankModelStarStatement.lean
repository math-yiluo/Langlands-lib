import Langlands.Representation.RankinSelberg.AdjacentRankModelStarStatement
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankIntegralModel
import Langlands.AllField.Representation.RankinSelberg.FunctionalEquationStatementSupplement
/-! The model-star identity of JPSS Section 6.2, with its Fourier action
character held fixed and its transformed coefficient argument expanded.
This module defines a proposition, not a proof. -/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding AdjacentRankModelStarStatement EqualRankAnalyticStatement EqualRankFunctionalEquationStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory TensorProduct
open Langlands.HarmonicAnalysis hiding PadicMatrixFourierSliceStatement PadicRowFourierSurjectivityStatement padicMatrixFourierSlice padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker
open Langlands.GeneralLinear

universe uF uV

/-- Source-derived fixed-Fourier-character formulation of JPSS (6.2.1).
The right coefficient is evaluated at `w * (h⁻¹)^ι`, without identifying
the resulting inverse-character coefficient with a standard-character one.
Both scalar integrands are required to be integrable. -/
def AdjacentRankModelStarStatement : Prop :=
  ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F],
    letI : MeasurableSpace F := borel F
    haveI : BorelSpace F := ⟨rfl⟩
    haveI : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
    haveI : TotallyDisconnectedSpace F := by
      let : NonarchimedeanRing F := by
        convert! ValuativeRel.nonarchimedeanRing F
        exact Valuation.toTopologicalSpace_eq _
      infer_instance
    ∀ (ψ : UnitaryAdditiveCharacter F)
      (ν : AdditiveHaarMeasure F) (hself : IsSelfDual ψ ν)
      (r : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (σ : Representation ℂ (GeneralLinear (r + 1) F) V),
      IsOfWhittakerType r (standardCharacter ψ r) σ →
      ∀ (ℓ : glFunctionals ψ r σ) (χ : Quasicharacter F)
        (Ψ : adjacentRankTestSpace ψ σ ℓ) (g : GeneralLinear (r + 2) F),
        letI : MeasurableSpace (GeneralLinear (r + 1) F) := borel _
        haveI : BorelSpace (GeneralLinear (r + 1) F) := ⟨rfl⟩
        let abv := normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)
        let η := generalLinearHaar F r
        let H := rectangularFourierEquiv ψ ν (r + 1) (r + 2) hself
        let ΨH : adjacentRankTestSpace ψ σ ℓ :=
          TensorProduct.map H.toLinearMap LinearMap.id Ψ
        let k := adjacentRankZeta F r * g
        let I : GeneralLinear (r + 1) F → ℂ := fun h =>
          adjacentRankTestEvaluation ψ σ ℓ
            (adjacentRankRho0 ψ ν hself σ ℓ k ΨH)
            (adjacentRankKernelMatrix h)
            (weylLong (r + 1) F * inverseTranspose (r + 1) F h⁻¹) *
            (χ⁻¹ (determinant h) : ℂ) * determinantWeight abv h ((r : ℂ) / 2)
        Langlands.AllField.RankinSelberg.Padic.AdjacentRankModelConverges F ψ ν hself σ ℓ χ Ψ
            (weylLong (r + 2) F * inverseTranspose (r + 2) F g) ∧
          Integrable I η ∧
          Langlands.AllField.RankinSelberg.Padic.adjacentRankModelIntegral F ψ ν hself σ ℓ χ Ψ
              (weylLong (r + 2) F * inverseTranspose (r + 2) F g) =
            (χ⁻¹ (determinant k) : ℂ) *
              determinantWeight abv k (((r + 1 : ℕ) : ℂ) / 2) * ∫ h, I h ∂η

end Langlands.AllField.RankinSelberg
