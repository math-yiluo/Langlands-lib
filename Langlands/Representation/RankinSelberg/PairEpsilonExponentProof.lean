import Langlands.Representation.RankinSelberg.PairEpsilonNormalizationStatement
import Langlands.Representation.RankinSelberg.PairFactorCharacterChangeProof
import Langlands.Representation.RankinSelberg.EqualRankEpsilonCharacterChangeStatement
import Langlands.Representation.RankinSelberg.UniformRankOneTwistProof
import Langlands.Representation.Whittaker.PadicCharacterIndependence
import Langlands.LocalFactor.Abelian.Scaling

/-!
# The exponent of the epsilon factor of a pair from the change of additive character

Bushnell, Henniart and Kutzko 1998, introduction (printed page 703): the
exponent of `ε(π × σ, s, ψ)` is `f(π × σ) + (r+1)(t+1) n(ψ)`, where
`f(π × σ)` does not depend on `ψ`. This module derives the Library statement
`PairEpsilonExponentStatement` from the change-of-character laws
`UnequalRankEpsilonCharacterChangeStatement` (Cogdell and Piatetski-Shapiro
1994, Lemma 2.1; proved in the Library as `pairFactorCharacterChange`) and
`EqualRankEpsilonCharacterChangeStatement`, which remains a hypothesis. Every
nontrivial additive character is `ψ₀^b` for a fixed `ψ₀` and some `b ∈ Fˣ`,
`n(ψ₀^b) = n(ψ₀) + ord b`, and the exponent changes by `(r+1)(t+1) ord b`.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear

universe uF uV uW

/-- The change-of-character law for epsilon factors of pairs of equal rank
implies the exponent formula of Bushnell, Henniart and Kutzko 1998
(introduction, printed page 703): for irreducible admissible `π` of
`GL_(r+1)(F)` and `σ` of `GL_(t+1)(F)` there is an integer `a` with
`m = a + (r+1)(t+1) n(ψ)` for every epsilon factor `ε(s, π × σ, ψ) = c q^(-ms)`
with a self-dual measure. The unequal-rank law is the Library theorem
`pairFactorCharacterChange`. -/
def PairEpsilonExponentReductionStatement : Prop :=
  EqualRankEpsilonCharacterChangeStatement.{uF, uV, uW} →
    PairEpsilonExponentStatement.{uF, uV, uW}

/-- The exponent formula from the two change-of-character laws. -/
theorem pairEpsilonExponent_of_characterChange
    (hU : UnequalRankEpsilonCharacterChangeStatement.{uF, uV, uW})
    (hE : EqualRankEpsilonCharacterChangeStatement.{uF, uV, uW}) :
    PairEpsilonExponentStatement.{uF, uV, uW} := by
  intro p _ F r t V _ _ W _ _ π σ hπi hπa hσi hσa
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  obtain ⟨ωπ, hωπ⟩ := UniformRankOneTwist.exists_hasGLCentralCharacter F π hπa hπi
  obtain ⟨ωσ, hωσ⟩ := UniformRankOneTwist.exists_hasGLCentralCharacter F σ hσa hσi
  -- The exponent part of the change law, for both rank orders.
  have hchange : ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
      (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
      (b : F.Carrierˣ)
      (ν' : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData (ψ.scale b))
      (e : ℂˣ × ℤ), IsPadicSymmetricEpsilonFactor F ψ ν.val π σ e →
      ∃ e' : ℂˣ × ℤ, IsPadicSymmetricEpsilonFactor F (ψ.scale b) ν'.val π σ e' ∧
        e'.2 = e.2 + ((r + 1) * (t + 1) : ℕ) *
          F.canonicalTopologicalData.ord (b : F.Carrier) := by
    intro ψ ν b ν' e he
    by_cases hrt : r = t
    · subst hrt
      obtain ⟨e', he', h2, -⟩ := hE p F r π σ ωπ ωσ hπi hπa hσi hσa hωπ hωσ ψ ν b ν' e he
      exact ⟨e', he', h2⟩
    · obtain ⟨e', he', h2, -⟩ :=
        hU p F r t π σ ωπ ωσ hrt hπi hπa hσi hσa hωπ hωσ ψ ν b ν' e he
      exact ⟨e', he', h2⟩
  by_cases hex : ∃ (ψ₀ : UnitaryAdditiveCharacter F.Carrier)
      (ν₀ : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ₀)
      (e₀ : ℂˣ × ℤ), IsPadicSymmetricEpsilonFactor F ψ₀ ν₀.val π σ e₀
  · obtain ⟨ψ₀, ν₀, e₀, he₀⟩ := hex
    refine ⟨e₀.2 - ((r + 1) * (t + 1) : ℕ) *
      F.canonicalTopologicalData.additiveConductor ψ₀, ?_⟩
    intro ψ ν e he
    obtain ⟨b, rfl⟩ := F.canonicalTopologicalData.exists_unit_scale_eq ψ₀ ψ
    obtain ⟨e', he', h2⟩ := hchange ψ₀ ν₀ b ν e₀ he₀
    rw [he.unique he', h2, F.canonicalTopologicalData.additiveConductor_scale ψ₀ b]
    ring
  · exact ⟨0, fun ψ ν e he => (hex ⟨ψ, ν, e, he⟩).elim⟩

/-- Proof of `PairEpsilonExponentReductionStatement`, with the unequal-rank law
`pairFactorCharacterChange.2`. -/
theorem pairEpsilonExponentReduction :
    PairEpsilonExponentReductionStatement.{uF, uV, uW} :=
  pairEpsilonExponent_of_characterChange pairFactorCharacterChange.2

end Langlands.RankinSelberg
