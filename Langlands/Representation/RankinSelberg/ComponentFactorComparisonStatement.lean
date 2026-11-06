import Langlands.Representation.RankinSelberg.TemperedLFactorStatement

/-!
# Pair-factor comparison for actual irreducible components

Internal consequences of smooth functional extension and the definitions of
pair factors. Both conclusions compare already-existing certificates.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear Polynomial

universe uF uV uW uV₂ uW₂

/-- Existing gamma certificates agree on smooth ambient representations and
actual components, and the component L-polynomial divides the ambient one.
The symmetric relations cover both rank orders. -/
def ComponentFactorComparisonStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
      AdditiveHaarMeasure F.Carrier)
    (r n : ℕ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {V₂ : Type uV₂} [AddCommGroup V₂] [Module ℂ V₂]
    {W₂ : Type uW₂} [AddCommGroup W₂] [Module ℂ W₂]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
    (ξ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V₂)
    (η : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W₂),
    (letI := F.canonicalTopologicalData.topology; IsSmooth ξ) →
    (letI := F.canonicalTopologicalData.topology; IsSmooth η) →
    IsIrreducibleComponent ξ π → IsIrreducibleComponent η σ →
    (∀ G H : RationalFunctions,
      IsPadicSymmetricGammaFactor F ψ ν π σ G →
      IsPadicSymmetricGammaFactor F ψ ν ξ η H → G = H) ∧
    (∀ P A : ℂ[X],
      IsPadicSymmetricLPolynomial F ψ ν π σ P →
      IsPadicSymmetricLPolynomial F ψ ν ξ η A → P ∣ A)

end Langlands.RankinSelberg
