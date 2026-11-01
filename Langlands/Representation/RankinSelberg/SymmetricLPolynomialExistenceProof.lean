import Langlands.Representation.RankinSelberg.SymmetricLPolynomialExistenceStatement
import Langlands.Representation.RankinSelberg.QuotientHaarExistence
import Langlands.Representation.Whittaker.CharacterChange
import Langlands.Representation.RankinSelberg.EqualRankAnalyticProof
import Langlands.Representation.RankinSelberg.UnequalRankAnalyticProof
import Langlands.Representation.RankinSelberg.UnequalRankCommonGeneratorProof

/-!
# Existence of symmetric p-adic L-polynomials

The published analytic theorems give a polynomial at the canonical quotient
measure. Character transport and uniqueness of compatible quotient measures
supply the full symmetric existence statement.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear Polynomial QuotientIntegration

universe uF uV uW

private theorem inverseWhittakerType {K : Type uF} [Field K]
    [TopologicalSpace K] [IsTopologicalRing K] {n : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ψ : UnitaryAdditiveCharacter K)
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) K) V)
    (hπ : IsOfWhittakerType n (standardCharacter ψ n) π) :
    IsOfWhittakerType n (inverseStandardCharacter ψ n) π := by
  refine ⟨hπ.1, hπ.2.1, ?_⟩
  obtain ⟨e⟩ := hπ.2.2
  have e' : Nonempty (glFunctionals (ψ.scale (-1)) n π ≃ₗ[ℂ] ℂ) :=
    ⟨(characterChangeFunctionalEquiv ψ π (-1)).symm.trans e⟩
  rw [← standardCharacter_scale_neg_one ψ n]
  exact e'

private theorem orderedLPolynomialExists
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
      AdditiveHaarMeasure F.Carrier)
    {r n : ℕ} {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
    (hnr : n ≤ r)
    (hπ : letI := F.canonicalTopologicalData.topology
      IsOfWhittakerType r (standardCharacter ψ r) π)
    (hσ : letI := F.canonicalTopologicalData.topology
      IsOfWhittakerType n (standardCharacter ψ n) σ) :
    ∃ P : ℂ[X], IsPadicPairLPolynomial F ψ ν π σ P := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  have hσ' := inverseWhittakerType ψ σ hσ
  have hex : PairLPolynomialExists F.canonicalTopologicalData.residueCardinality ψ
      (normalizedAbsoluteValue F.canonicalTopologicalData)
      (unipotentQuotientHaar F.Carrier n) ν π σ := by
    rcases hnr.lt_or_eq with hlt | heq
    · exact (unequalRankCommonGenerator.{uF,uV,uW}
        F F.canonicalTopologicalData n r).pairLPolynomialExists
        (fun j k _ => unequalRankAnalytic.{uF,uV,uW} F F.canonicalTopologicalData n j k)
        hlt ψ
        (unipotentQuotientHaar F.Carrier n)
        (unipotentQuotientHaar_isCompatible F.Carrier n) ν V W π σ hπ hσ'
    · subst r
      exact (equalRankAnalytic.{uF,uV,uW}
        F F.canonicalTopologicalData n).pairLPolynomialExists
        ψ (unipotentQuotientHaar F.Carrier n)
        (unipotentQuotientHaar_isCompatible F.Carrier n) ν V W π σ hπ hσ'
  obtain ⟨P, hP⟩ := hex
  refine ⟨P, ?_, ?_⟩
  · exact quotientHaarExistence F F.canonicalTopologicalData n
  · intro _ μ hμ
    rw [unipotentQuotientHaar_unique F.Carrier n μ hμ]
    exact hP

/-- Every pair of Whittaker-type representations has one symmetric p-adic
L-polynomial for all compatible quotient measures. -/
theorem symmetricLPolynomialExists :
    SymmetricLPolynomialExistenceStatement.{uF,uV,uW} := by
  intro p hp F ψ ν r n V _ _ W _ _ π σ hπ hσ
  by_cases hnr : n ≤ r
  · obtain ⟨P, hP⟩ := orderedLPolynomialExists.{uF,uV,uW}
      F ψ ν.val π σ hnr hπ hσ
    exact ⟨P, by simpa only [IsPadicSymmetricLPolynomial, ite_eq_left hnr] using hP⟩
  · obtain ⟨P, hP⟩ := orderedLPolynomialExists.{uF,uW,uV}
      F ψ ν.val σ π (Nat.le_of_lt (Nat.lt_of_not_ge hnr)) hσ hπ
    exact ⟨P, by simpa only [IsPadicSymmetricLPolynomial, ite_eq_right hnr] using hP⟩

end Langlands.RankinSelberg
