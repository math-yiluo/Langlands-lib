import Langlands.Representation.RankinSelberg.CanonicalPairLFactor
import Langlands.AllField.Representation.RankinSelberg.CanonicalCharacterChange
import Langlands.AllField.Representation.RankinSelberg.PairLFactor
/-!
# Canonical pair L-factors and additive-character scaling
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding CharacterChangeCompatibleMeasureStatement CharacterChangeRectangularHaarStatement CharacterChangeRectangularProductStatement EqualRankAnalyticStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement UnipotentCharacterChangeModulusStatement characterChangeCompatibleMeasure characterChangeCompatibleMeasure_of_unipotentModulus characterChangeRectangularHaarStatement characterChangeRectangularProductStatement isEqualRankLPolynomial_characterChange_canonical isEqualRankLPolynomial_characterChange_normalized isPairLPolynomial_characterChange_canonical isUnequalRankLPolynomial_characterChange_canonical leviModulus_characterChangeLevi leviModulus_characterChangeLevi_eq_pow normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow unipotentCharacterChangeModulus unipotentQuotientHaar_characterChange unipotentQuotientHaar_sigmaFinite_normalized zetaSpan_equalRank_characterChange_canonical zetaSpan_equalRank_characterChange_normalized zetaSpan_unequalRank_characterChange_canonical
open Langlands.AllField.RankinSelberg

open Langlands.GeneralLinear
open Langlands.Whittaker
open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open _root_.MeasureTheory _root_.Polynomial

universe uF uV uW

variable {K : Type uF} [Field K] (T : LocalFieldData K)

/-- Character scaling preserves the common normalized polynomial for every block. -/
theorem isPairLPolynomial_characterChange_canonical (n r : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel (Langlands.GeneralLinear (n + 1) K)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1) K) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1) K)
    letI : BorelSpace (upperUnipotent (n + 1) K) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient n K)
    letI : BorelSpace (LeftUnipotentQuotient n K) := ⟨rfl⟩
    letI := T.secondCountableTopology
    letI := borel K
    letI : BorelSpace K := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter K) (a : Kˣ)
  (ν : AdditiveHaarMeasure K)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (π : Representation ℂ (Langlands.GeneralLinear (r + 1) K) V)
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) K) W) (P : ℂ[X]),
      IsPairLPolynomial T.residueCardinality ψ (normalizedAbsoluteValue T)
        (unipotentQuotientHaar K n) ν π σ P ↔
      IsPairLPolynomial T.residueCardinality (ψ.scale a) (normalizedAbsoluteValue T)
        (unipotentQuotientHaar K n) ν π σ P := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel (Langlands.GeneralLinear (n + 1) K)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) K) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) K)
  let : BorelSpace (upperUnipotent (n + 1) K) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n K)
  let : BorelSpace (LeftUnipotentQuotient n K) := ⟨rfl⟩
  let := T.secondCountableTopology
  let := borel K
  let : BorelSpace K := ⟨rfl⟩
  intro ψ a ν V _ _ W _ _ π σ P
  by_cases hnr : n < r
  · rw [isPairLPolynomial_of_lt hnr, isPairLPolynomial_of_lt hnr]
    refine forall_congr' fun j => forall_congr' fun k => forall_congr' fun hr => ?_
    subst hr
    exact isUnequalRankLPolynomial_characterChange_canonical T n j k ψ a ν V W π σ P
  · by_cases hrn : r = n
    · subst r
      rw [isPairLPolynomial_self, isPairLPolynomial_self]
      exact isEqualRankLPolynomial_characterChange_canonical T n ψ a V W π σ P
    · exact iff_of_false (not_isPairLPolynomial_of_lt (by omega))
        (not_isPairLPolynomial_of_lt (by omega))

end Langlands.AllField.RankinSelberg
