import Langlands.Representation.RankinSelberg.SymmetricGammaExpressionStatement

/-!
# The canonical expression characterizes symmetric gamma certificates

The original and dual analytic inputs remain in the construction premise.
The supplied intrinsic polynomial certificates determine the rational expression.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear Polynomial QuotientIntegration

universe uF uV uW

set_option maxHeartbeats 800000 in
/-- Arbitrary certified epsilon data and original/dual polynomials give the
canonical gamma certificate for an ordered pair under its construction input. -/
theorem IsPadicPairEpsilonFactor.gammaFactor_of_constructionInput
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
      AdditiveHaarMeasure F.Carrier)
    {r n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
    (h : PadicPairGammaConstructionInput F ψ ν π σ)
    {e : ℂˣ × ℤ} {P Pdual : ℂ[X]}
    (he : IsPadicPairEpsilonFactor F ψ ν π σ e)
    (hP : IsPadicPairLPolynomial F ψ ν π σ P)
    (hPd : letI := F.canonicalTopologicalData.topology
      letI := F.canonicalTopologicalData.valuativeRel
      letI := F.canonicalTopologicalData.localField
      IsPadicPairLPolynomial F (ψ.scale (-1)) ν
      (inverseTransposePullback π) (inverseTransposePullback σ) Pdual) :
    IsPadicPairGammaFactor F ψ ν π σ
      (rationalGammaExpression (LocalFactor.residueReflection F) e.1 e.2 P Pdual) := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := F.canonicalTopologicalData.fieldT2
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  obtain ⟨hnr, _, _, hπ, hσ, hA, hAd⟩ := h
  have hπd := isOfWhittakerType_firstDual ψ π hπ
  have hσd := isOfWhittakerType_secondDual ψ σ hσ
  have hμ := unipotentQuotientHaar_isCompatible F.Carrier n
  have hP' := hP.2 (unipotentQuotientHaar F.Carrier n) hμ
  have hPd' := hPd.2 (unipotentQuotientHaar F.Carrier n) hμ
  have hq := F.canonicalTopologicalData.residueCardinality_gt_one
  change IsPairGammaFactor _ _ _ _ _ _ _
  by_cases hr : r = n
  · subst r
    simp only [PairAnalyticInput] at hA hAd
    apply isPairGammaFactor_self.mpr
    exact IsEqualRankEpsilonFactor.gammaFactor hπ hσ hπd hσd hA
      (fun ℓ ℓ' hℓ hℓ' => hAd _ _ (firstDualFunctional_ne_zero ψ π hℓ)
        (secondDualFunctional_ne_zero ψ σ hℓ'))
      hq (LocalFactor.coe_residueReflection F) hμ
      (isPairEpsilonFactor_self.mp he)
      (isPairLPolynomial_self.mp hP') (isPairLPolynomial_self.mp hPd')
  · have hlt : n < r := by omega
    simp only [PairAnalyticInput, dite_eq_right hr] at hA hAd
    apply (isPairGammaFactor_of_lt hlt).mpr
    exact IsUnequalRankEpsilonFactor.gammaFactor hlt hπ hσ hπd hσd hA
      (fun ℓ ℓ' hℓ hℓ' => hAd _ _ (firstDualFunctional_ne_zero ψ π hℓ)
        (secondDualFunctional_ne_zero ψ σ hℓ'))
      hq (LocalFactor.coe_residueReflection F) hμ
      ((isPairEpsilonFactor_of_lt hlt).mp he) hP' hPd'

/-- Every symmetric gamma certificate is exactly the canonical expression of any
supplied epsilon and original/dual polynomial certificates. -/
theorem symmetricGammaExpression :
    SymmetricGammaExpressionStatement.{uF,uV,uW} := by
  intro p _ F ψ ν r n V _ _ W _ _ π σ
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  intro h e P Pdual he hP hPd G
  have hG : IsPadicSymmetricGammaFactor F ψ ν.val π σ
      (rationalGammaExpression (LocalFactor.residueReflection F) e.1 e.2 P Pdual) := by
    by_cases hnr : n ≤ r
    · apply (isPadicSymmetricGammaFactor_of_le hnr).mpr
      apply IsPadicPairEpsilonFactor.gammaFactor_of_constructionInput F ψ ν.val π σ
      · simpa only [PadicSymmetricGammaConstructionInput, ite_eq_left hnr] using h
      · exact (isPadicSymmetricEpsilonFactor_of_le hnr).mp he
      · exact (isPadicSymmetricLPolynomial_of_le hnr).mp hP
      · exact (isPadicSymmetricLPolynomial_of_le hnr).mp hPd
    · have hlt : r < n := Nat.lt_of_not_ge hnr
      apply (isPadicSymmetricGammaFactor_of_lt hlt).mpr
      apply IsPadicPairEpsilonFactor.gammaFactor_of_constructionInput F ψ ν.val σ π
      · simpa only [PadicSymmetricGammaConstructionInput, ite_eq_right hnr] using h
      · exact (isPadicSymmetricEpsilonFactor_of_lt hlt).mp he
      · exact (isPadicSymmetricLPolynomial_of_lt hlt).mp hP
      · exact (isPadicSymmetricLPolynomial_of_lt hlt).mp hPd
  constructor
  · intro hG'
    exact hG'.unique hG
  · intro hEq
    simpa only [hEq] using hG

end Langlands.RankinSelberg
