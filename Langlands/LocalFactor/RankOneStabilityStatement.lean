import Langlands.LocalFactor.Abelian.Padic

/-!
# Rank-one highly ramified twist stability

The rank-one specialization of Deligne--Henniart, Theorem 4.6, stated
using the actual unit filtration, conductors, and fixed-Haar Gauss factor.
These are proposition definitions, not proofs of stability.
-/

noncomputable section

open MeasureTheory

namespace Langlands.LocalFactor

universe u

section Witness

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p}
  (T : F.TopologicalData)

local notation "MultiplicativeCharacter" =>
  @HarmonicAnalysis.Quasicharacter F.Carrier _ T.topology
local notation "AdditiveCharacter" =>
  @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology

/-- A specification of the twisting element through the actual epsilon
expression. No witness or local-constant existence theorem is assumed.
Every supplied regular additive Haar measure is retained unchanged. -/
def RankOneTwistWitness (χ : MultiplicativeCharacter)
    (ψ : AdditiveCharacter) (γ : F.Carrierˣ) : Prop :=
  letI := T.topology
  letI := borel F.Carrier
  ∀ η : HarmonicAnalysis.Quasicharacter F.Carrier,
    2 * T.multiplicativeConductor η ≤ T.multiplicativeConductor χ →
    ∀ μ : HarmonicAnalysis.AdditiveHaarMeasure F.Carrier, ∀ s : ℂ,
      PadicAbelian.epsilon T (χ * η) ψ μ.measure s =
        (η γ : ℂ) * PadicAbelian.epsilon T χ ψ μ.measure s

end Witness

/-- Rank-one wild stability, with its precise integer ramification bound,
the valuation of the twisting element, and its full uniqueness coset.
The equality of the separate L factors is stated on their everywhere regular
ramified domain. The prime and finite-extension carrier universe are arbitrary. -/
def RankOneStabilityStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p)
    (T : F.TopologicalData),
    letI := T.topology
    letI := borel F.Carrier
    ∀ (χ : HarmonicAnalysis.Quasicharacter F.Carrier)
      (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier),
      2 ≤ T.multiplicativeConductor χ →
      (∀ η : HarmonicAnalysis.Quasicharacter F.Carrier,
        2 * T.multiplicativeConductor η ≤ T.multiplicativeConductor χ →
        T.multiplicativeConductor (χ * η) = T.multiplicativeConductor χ ∧
        PadicAbelian.rationalLFactor T χ = 1 ∧
        PadicAbelian.rationalLFactor T (χ * η) = 1 ∧
        ∀ s : ℂ, PadicAbelian.lFactor T χ s = 1 ∧
          PadicAbelian.lFactor T (χ * η) s = 1) ∧
      ∃ γ : F.Carrierˣ,
        T.ord (γ : F.Carrier) =
          (T.multiplicativeConductor χ : ℤ) + T.additiveConductor ψ ∧
        RankOneTwistWitness T χ ψ γ ∧
        ∀ γ' : F.Carrierˣ, RankOneTwistWitness T χ ψ γ' ↔
          γ' * γ⁻¹ ∈ T.principalUnits (T.multiplicativeConductor χ / 2)

end Langlands.LocalFactor
