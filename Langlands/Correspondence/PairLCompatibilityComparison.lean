import Langlands.Correspondence.AutomorphicPairFactors
import Langlands.Representation.RankinSelberg.PairLFactorCharacterizationStatement

/-!
# Comparing compatible pair L-polynomials

Supporting helper material for the assembly characterization proof. These lemmas
compare already supplied compatibility certificates; they do not establish
assembly inheritance, classification, or the characterization statement.
-/

noncomputable section

namespace Langlands.Correspondence

universe uF uP uA

open Polynomial

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  {ψ : NontrivialAdditiveCharacter F} {r t : ℕ}
  {D : WeilDeligneClass.{uF, uP} F r.succPNat}
  {D' : WeilDeligneClass.{uF, uP} F t.succPNat}
  {π ρ : AutomorphicClass.{uF, uA} F r.succPNat}
  {π' ρ' : AutomorphicClass.{uF, uA} F t.succPNat}

/-- At any supplied self-dual measure, two pairs compatible with the same
parameter pair admit the same certified L-polynomial. -/
theorem IsPairLCompatibleAt.common_polynomial
    (hπ : IsPairLCompatibleAt F ψ D D' π π')
    (hρ : IsPairLCompatibleAt F ψ D D' ρ ρ')
    (ν : LocalAdditiveHaarMeasure F) (hν : IsSelfDualMeasure F ψ ν) :
    ∃ P : ℂ[X], IsAutomorphicPairLPolynomial F ψ ν π π' P ∧
      IsAutomorphicPairLPolynomial F ψ ν ρ ρ' P := by
  obtain ⟨P, hP, hPa⟩ := hπ.2 ν hν
  obtain ⟨Q, hQ, hQa⟩ := hρ.2 ν hν
  have hPQ : P = Q :=
    RatFunc.algebraMap_injective ℂ (inv_inj.mp (hPa.symm.trans hQa))
  exact ⟨P, hP, hPQ ▸ hQ⟩

/-- The common-polynomial comparison supplies the pole-order test appearing in
the representation-side square-integrable characterization. -/
theorem IsPairLCompatibleAt.same_pole_order
    (hπ : IsPairLCompatibleAt F ψ D D' π π')
    (hρ : IsPairLCompatibleAt F ψ D D' ρ ρ')
    (ν : LocalAdditiveHaarMeasure F) (hν : IsSelfDualMeasure F ψ ν) :
    ∃ P Q : ℂ[X], IsAutomorphicPairLPolynomial F ψ ν π π' P ∧
      IsAutomorphicPairLPolynomial F ψ ν ρ ρ' Q ∧
      RankinSelberg.lPolynomialPoleOrderAtZero P =
        RankinSelberg.lPolynomialPoleOrderAtZero Q := by
  obtain ⟨P, hP, hQ⟩ := hπ.common_polynomial hρ ν hν
  exact ⟨P, P, hP, hQ, rfl⟩

end Langlands.Correspondence
