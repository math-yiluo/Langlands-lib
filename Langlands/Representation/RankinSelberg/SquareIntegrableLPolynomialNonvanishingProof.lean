import Langlands.Representation.RankinSelberg.SquareIntegrableLPolynomialNonvanishingStatement
import Langlands.Representation.RankinSelberg.SquareIntegrableEqualRankAnalyticProof
import Langlands.Representation.RankinSelberg.SquareIntegrableZeroRowAnalyticProof
import Langlands.Representation.RankinSelberg.HolomorphicRationalContinuationProof
import Langlands.Representation.RankinSelberg.NormalizedGeneratorRegularityProof

/-!
# Nonvanishing of existing square-integrable pair L-polynomials

The intrinsic value sets supply the coefficient-model witnesses required by
sharp holomorphy. Their rational continuations are regular in the punctured
unit disk, so the normalized denominator cannot vanish there. Its constant
coefficient handles zero. Polynomial existence is a separate obligation.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration Polynomial

universe uF uV uW

variable {p : ℕ} [Fact p.Prime]

section Pair

variable {F : PadicField.{uF} p}
  {ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier}
  {ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
    AdditiveHaarMeasure F.Carrier}
  {r t : ℕ} {V : Type uV} {W : Type uW}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W}
  {P : ℂ[X]}

/-- Every existing ordered-pair L-polynomial of an irreducible square-integrable
pair has no zero in the open unit disk. The supplied additive Haar measure need
not be self-dual. -/
theorem IsPadicPairLPolynomial.eval_ne_zero_of_squareIntegrable
    (hP : IsPadicPairLPolynomial F ψ ν π σ P)
    (hiπ : Representation.IsIrreducible π)
    (hsπ : F.canonicalTopologicalData.IsSquareIntegrable π)
    (hiσ : Representation.IsIrreducible σ)
    (hsσ : F.canonicalTopologicalData.IsSquareIntegrable σ)
    {z : ℂ} (hz : ‖z‖ < 1) : P.eval z ≠ 0 := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (t + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (t + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (t + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (t + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient t F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient t F.Carrier) := ⟨rfl⟩
  obtain ⟨⟨_, μ, hμ⟩, hP⟩ := hP
  have hPair := hP μ hμ
  by_cases hz0 : z = 0
  · subst z
    rw [← Polynomial.coeff_zero_eq_eval_zero, hPair.coeff_zero]
    exact one_ne_zero
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hq := PadicField.TopologicalData.residueCardinality_gt_one
    F.canonicalTopologicalData
  by_cases htr : t < r
  · obtain ⟨k, hr⟩ : ∃ k : ℕ, r = t + (0 + k + 1) := ⟨r - t - 1, by omega⟩
    subst r
    have hgen := hPair.isUnequalRankLPolynomial 0 k
    apply hgen.eval_ne_zero_of_regularAt hz0
    intro R hR
    rcases hR with ⟨f, ⟨ℓ, hf⟩, f', ⟨ℓ', hf'⟩, _, hR⟩
    have hhol := (squareIntegrableZeroRowAnalytic p F F.canonicalTopologicalData
      t k ψ μ hμ ν V W π σ hiπ hsπ hiσ hsσ ℓ ℓ' ⟨f, hf⟩ ⟨f', hf'⟩).2
    exact (holomorphicRationalContinuation _ hq _ R hhol hR).2 z hzpos hz
  · by_cases hrt : r = t
    · subst r
      have hgen := isPairLPolynomial_self.mp hPair
      apply hgen.eval_ne_zero_of_regularAt hz0
      intro R hR
      rcases hR with ⟨f, ⟨ℓ, hf⟩, f', ⟨ℓ', hf'⟩, Φ, _, hR⟩
      have hhol := (squareIntegrableEqualRankAnalytic p F F.canonicalTopologicalData
        t ψ μ hμ V W π σ hiπ hsπ hiσ hsσ ℓ ℓ' ⟨f, hf⟩ ⟨f', hf'⟩ Φ).2
      exact (holomorphicRationalContinuation _ hq _ R hhol hR).2 z hzpos hz
    · exact (not_isPairLPolynomial_of_lt (by omega) hPair).elim

/-- The symmetric rank convention preserves square-integrable nonvanishing. -/
theorem IsPadicSymmetricLPolynomial.eval_ne_zero_of_squareIntegrable
    (hP : IsPadicSymmetricLPolynomial F ψ ν π σ P)
    (hiπ : Representation.IsIrreducible π)
    (hsπ : F.canonicalTopologicalData.IsSquareIntegrable π)
    (hiσ : Representation.IsIrreducible σ)
    (hsσ : F.canonicalTopologicalData.IsSquareIntegrable σ)
    {z : ℂ} (hz : ‖z‖ < 1) : P.eval z ≠ 0 := by
  by_cases htr : t ≤ r
  · exact ((isPadicSymmetricLPolynomial_of_le htr).mp hP).eval_ne_zero_of_squareIntegrable hiπ hsπ hiσ hsσ hz
  · exact ((isPadicSymmetricLPolynomial_of_lt (Nat.lt_of_not_ge htr)).mp hP).eval_ne_zero_of_squareIntegrable hiσ hsσ hiπ hsπ hz

end Pair

/-- Every existing symmetric L-polynomial of an irreducible square-integrable
pair is nonvanishing throughout the open unit disk. -/
theorem squareIntegrableLPolynomialNonvanishing :
    SquareIntegrableLPolynomialNonvanishingStatement.{uF,uV,uW} := by
  intro p _ F ψ ν r t V _ _ W _ _ π σ hiπ hsπ hiσ hsσ P hP z hz
  exact hP.eval_ne_zero_of_squareIntegrable hiπ hsπ hiσ hsσ hz

end Langlands.RankinSelberg
