import Langlands.Representation.RankinSelberg.SegmentGammaTelescopingStatement
import Langlands.Representation.RankinSelberg.UnitaryContragredientTwistParameters
import Langlands.Representation.Whittaker.DualTransform

noncomputable section

namespace Langlands.RankinSelberg

open Polynomial GeneralLinear Whittaker HarmonicAnalysis SegmentGammaTelescoping

universe uF uV uW

/-- The original and inverse-transpose dual equal-rank L-polynomials use
inverse finite parameter sets; unitary inputs give unit-circle parameters. -/
def SupercuspidalParameterProductStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (r : ℕ) {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) W),
    π.IsIrreducible →
    (letI := F.canonicalTopologicalData.topology; IsSupercuspidal π) →
    σ.IsIrreducible →
    (letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType r (standardCharacter ψ r) σ) →
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    letI := F.canonicalTopologicalData.localField
    ∃ A : Finset ℂˣ,
      (∀ a : ℂˣ, a ∈ A ↔ IsContragredientTwistParameter F π σ (a : ℂ)) ∧
      IsPadicPairLPolynomial F ψ ν.val π σ (∏ a ∈ A, linearFactor a) ∧
      IsPadicPairLPolynomial F (ψ.scale (-1)) ν.val
        (inverseTransposePullback π) (inverseTransposePullback σ)
        (∏ a ∈ A, linearFactor a⁻¹) ∧
      (IsUnitarizable π → IsUnitarizable σ → ∀ a ∈ A, ‖(a : ℂ)‖ = 1)

end Langlands.RankinSelberg
