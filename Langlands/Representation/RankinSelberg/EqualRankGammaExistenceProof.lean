import Langlands.Representation.RankinSelberg.EqualRankGammaExistenceReduction
import Langlands.Representation.RankinSelberg.EqualRankGammaExistenceStatement
import Langlands.Representation.RankinSelberg.EqualRankAnalyticProof
import Langlands.Representation.RankinSelberg.EqualRankContinuedFormsProof
import Langlands.Representation.RankinSelberg.EqualRankTrilinearUniquenessProof
import Langlands.Representation.RankinSelberg.GammaFromWhittakerType
import Langlands.HarmonicAnalysis.RowFourierCompatibilityProof

/-!
# Equal-rank JPSS gamma-factor existence

Combine the proved analytic continuation, Fourier compatibility, normalized
continued forms and trilinear uniqueness on the supplied coefficient models.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF uV uW

/-- A single rational gamma comparison for all equal-rank test triples,
with the supplied topology, quotient measure and self-dual Fourier measure. -/
theorem equalRankGammaExistence
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ) :
    EqualRankGammaExistenceStatement.{uF,uV,uW} F T n := by
  have hAnalytic := equalRankAnalytic.{uF,uV,uW} F T n
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := IsTopologicalAddGroup.rightUniformSpace F.Carrier
  let := isUniformAddGroup_of_addCommGroup (G := F.Carrier)
  let := equalRankGamma_valuative_nonarchimedean (K := F.Carrier)
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  unfold EqualRankGammaExistenceStatement
  intro ψ hRight μ hμ ν hν V _ _ W _ _ π σ hπ hσ ℓ ℓ' hℓ hℓ'
  have hA := hAnalytic ψ μ hμ V W π σ hπ hσ ℓ ℓ' hℓ hℓ'
  have hAd := hAnalytic (ψ.scale (-1)) μ hμ V W
    (inverseTransposePullback π) (inverseTransposePullback σ)
    (isOfWhittakerType_firstDual ψ π hπ) (isOfWhittakerType_secondDual ψ σ hσ)
    (firstDualFunctional ψ π ℓ) (secondDualFunctional ψ σ ℓ')
    (firstDualFunctional_ne_zero ψ π hℓ) (secondDualFunctional_ne_zero ψ σ hℓ')
  have hF := (rowFourierCompatibility ψ ν (n + 1) hν).1
  obtain ⟨P, hP⟩ := hA.2.2.2
  obtain ⟨Pd, hPd⟩ := hAd.2.2.2
  have hPdual : IsNormalizedGenerator
      (dualEqualRankRationalValues T.residueCardinality ψ
        (normalizedAbsoluteValue T) μ π σ ℓ ℓ') Pd := by
    simpa only [dualEqualRankRationalValues_eq] using hPd
  obtain ⟨B, Bd, hInv, hEval⟩ :=
    equalRankContinuedForms F T n ψ μ hμ ν V W π σ hπ hσ ℓ ℓ' hℓ hℓ'
      hA hAd hF P Pd hP hPdual
  obtain ⟨E, hE⟩ := equalRankTrilinearUniqueness F T n ψ V W π σ hπ hσ ℓ ℓ'
  exact EqualRankGammaReduction.gammaEquation_of_continuedForms T.residueCardinality_gt_one hσ hA hAd hF
    P Pd hP hPdual.polynomial_ne_zero B Bd
    (fun f f' Φ Φhat R Rd hPair hR hRd s =>
      hEval f f' Φ Φhat hPair R Rd hR hRd s)
    E (fun s hs => hE s hs (B s) (Bd s) (hInv s).1 (hInv s).2)

end Langlands.RankinSelberg
