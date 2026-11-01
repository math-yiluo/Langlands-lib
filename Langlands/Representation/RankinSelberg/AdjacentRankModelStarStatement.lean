import Langlands.Representation.RankinSelberg.AdjacentRankStarData
import Langlands.Representation.RankinSelberg.Measures

/-! The model-star identity of JPSS Section 6.2, with its Fourier action
character held fixed and its transformed coefficient argument expanded.
This module defines a proposition, not a proof. -/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker TensorProduct GeneralLinear

universe uF uV

/-- Source-derived fixed-Fourier-character formulation of JPSS (6.2.1).
The right coefficient is evaluated at `w * (h⁻¹)^ι`, without identifying
the resulting inverse-character coefficient with a standard-character one.
Both scalar integrands are required to be integrable. -/
def AdjacentRankModelStarStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p),
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    letI := F.canonicalTopologicalData.localField
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    haveI : BorelSpace F.Carrier := ⟨rfl⟩
    haveI : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
    haveI : TotallyDisconnectedSpace F.Carrier := by
      let : NonarchimedeanRing F.Carrier := by
        convert! ValuativeRel.nonarchimedeanRing F.Carrier
        exact Valuation.toTopologicalSpace_eq _
      infer_instance
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
      (ν : AdditiveHaarMeasure F.Carrier) (hself : IsSelfDual ψ ν)
      (r : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V),
      IsOfWhittakerType r (standardCharacter ψ r) σ →
      ∀ (ℓ : glFunctionals ψ r σ) (χ : Quasicharacter F.Carrier)
        (Ψ : adjacentRankTestSpace ψ σ ℓ) (g : GeneralLinear (r + 2) F.Carrier),
        letI : MeasurableSpace (GeneralLinear (r + 1) F.Carrier) := borel _
        haveI : BorelSpace (GeneralLinear (r + 1) F.Carrier) := ⟨rfl⟩
        let abv := normalizedAbsoluteValue F.canonicalTopologicalData
        let η := generalLinearHaar F.Carrier r
        let H := rectangularFourierEquiv ψ ν (r + 1) (r + 2) hself
        let ΨH : adjacentRankTestSpace ψ σ ℓ :=
          TensorProduct.map H.toLinearMap LinearMap.id Ψ
        let k := adjacentRankZeta F.Carrier r * g
        let I : GeneralLinear (r + 1) F.Carrier → ℂ := fun h =>
          adjacentRankTestEvaluation ψ σ ℓ
            (adjacentRankRho0 ψ ν hself σ ℓ k ΨH)
            (adjacentRankKernelMatrix h)
            (weylLong (r + 1) F.Carrier * inverseTranspose (r + 1) F.Carrier h⁻¹) *
            (χ⁻¹ (determinant h) : ℂ) * determinantWeight abv h ((r : ℂ) / 2)
        Padic.AdjacentRankModelConverges F ψ ν hself σ ℓ χ Ψ
            (weylLong (r + 2) F.Carrier * inverseTranspose (r + 2) F.Carrier g) ∧
          Integrable I η ∧
          Padic.adjacentRankModelIntegral F ψ ν hself σ ℓ χ Ψ
              (weylLong (r + 2) F.Carrier * inverseTranspose (r + 2) F.Carrier g) =
            (χ⁻¹ (determinant k) : ℂ) *
              determinantWeight abv k (((r + 1 : ℕ) : ℂ) / 2) * ∫ h, I h ∂η

end Langlands.RankinSelberg
