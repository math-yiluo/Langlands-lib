import Langlands.Representation.Character.SeparationProof
import Langlands.Representation.RankinSelberg.HighlyRamified.Uniform
import Langlands.Representation.RankinSelberg.PairEpsilonExponentProof
import Langlands.Representation.RankinSelberg.StableTwist.JPSSStability

/-! # Standard factors of a sufficiently ramified determinant twist -/

noncomputable section

set_option autoImplicit false

namespace Langlands.BaseChange

open HarmonicAnalysis GeneralLinear RankinSelberg
open LocalFactor.PadicAbelian (epsilonExponent)
open Polynomial

universe u uV

/-- A sufficiently ramified determinant twist of a generic representation has
standard Euler polynomial one and epsilon exponent equal to the rank times
the Tate exponent of the twisting character. The additive character is arbitrary. -/
def HighlyRamifiedStandardFactorsStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p),
    letI := F.canonicalTopologicalData.topology
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (r : ℕ)
      (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V),
      Whittaker.IsGeneric ψ r π →
      ∃ B : ℕ, ∀ (χ : Quasicharacter F.Carrier),
        B ≤ F.canonicalTopologicalData.multiplicativeConductor χ →
        let πχ := twist (χ.toMonoidHom.comp determinant) π
        let trivial := rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)
        ∀ (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ),
          (∀ P : ℂ[X], IsPadicSymmetricLPolynomial F ψ ν.val πχ trivial P → P = 1) ∧
          (∀ e : ℂˣ × ℤ, IsPadicSymmetricEpsilonFactor F ψ ν.val πχ trivial e →
            e.2 = (r + 1 : ℕ) * epsilonExponent F.canonicalTopologicalData χ ψ)

set_option maxHeartbeats 1700000 in
/-- Apply the uniform rank-one twist formula at additive conductor zero and
transport the polynomial and the integer exponent to the given character. -/
theorem highlyRamifiedStandardFactors : HighlyRamifiedStandardFactorsStatement.{u, uV} := by
  intro p _ F
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro ψ r V _ _ π hπ
  let := CharacterSeparation.nontrivial_of_isIrreducible hπ.1
  obtain ⟨m, hm⟩ := HighlyRamified.exists_hasPrincipalLevelVector F π hπ.2.1.1
  obtain ⟨ψ₀, a, h₀, rfl⟩ := StableTwist.exists_conductorZero_scale F ψ
  obtain ⟨ν₀⟩ := HighlyRamified.nonempty_selfDualHaar F ψ₀
  have hπ₀ := (T.isGeneric_iff_character π ψ₀ (ψ₀.scale a)).mpr hπ
  obtain ⟨B, hB, -⟩ := UniformRankOneTwist.uniformRankOneTwist.{u, uV} p F ψ₀ ν₀ h₀ r m
  refine ⟨B, ?_⟩
  intro χ hχ πχ trivial ν
  obtain ⟨hP₀, c, he₀⟩ := hB π hπ₀ hm χ hχ
  refine ⟨fun P hP => ?_, fun e he => ?_⟩
  · have hP₁ := (Padic.isPadicSymmetricLPolynomial_characterChange F ψ₀ a ν₀.val πχ trivial 1).mp hP₀
    exact hP.unique_of_measure hP₁
  · have hπχ := UniformRankOneTwist.isGeneric_twist F ψ₀ π hπ₀ χ
    have htrivial := UniformRankOneTwist.isGeneric_rankOneCharacter_one F ψ₀
    obtain ⟨b, hb⟩ := pairEpsilonExponent_of_characterChange.{u, uV, 0}
      pairFactorCharacterChange.2 equalRankEpsilonCharacterChange p F r 0 πχ trivial
      hπχ.1 hπχ.2.1 htrivial.1 htrivial.2.1
    have had := hb ψ₀ ν₀ _ he₀
    simp only [h₀, mul_zero, add_zero] at had
    rw [hb _ ν e he, ← had]
    push_cast
    simp only [mul_one, epsilonExponent]
    ring

end Langlands.BaseChange
