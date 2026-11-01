import Langlands.Representation.RankinSelberg.WhittakerGammaAdapters
import Langlands.Representation.RankinSelberg.EqualRankAnalyticProof
import Langlands.Representation.RankinSelberg.UnequalRankAnalyticProof
import Langlands.Representation.RankinSelberg.EqualRankFunctionalEquationProof
import Langlands.Representation.RankinSelberg.UnequalRankFunctionalEquationProof
import Langlands.Representation.RankinSelberg.WhittakerTypeGammaConstructionInputStatement

/-! Canonical symmetric gamma construction inputs from the published JPSS
analytic and functional-equation theorems. -/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF uV uW

/-- Whittaker type supplies all canonical construction inputs when the larger
rank is first and the second representation has inverse-standard type. -/
theorem padicPairGammaConstructionInput_of_whittakerType
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (r n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (W : Type uW) [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
    (hnr : n ≤ r) :
    letI := F.canonicalTopologicalData.topology
    IsOfWhittakerType r (standardCharacter ψ r) π →
    IsOfWhittakerType n (inverseStandardCharacter ψ n) σ →
    PadicPairGammaConstructionInput F ψ ν.val π σ := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := F.canonicalTopologicalData.fieldT2
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  intro hπ hσ
  have hμ := unipotentQuotientHaar_isCompatible F.Carrier n
  have hA :
      ∀ (χ : UnitaryAdditiveCharacter F.Carrier)
        (ρ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
        (τ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W),
        IsOfWhittakerType r (standardCharacter χ r) ρ →
        IsOfWhittakerType n (inverseStandardCharacter χ n) τ →
        PairAnalyticInput F.canonicalTopologicalData.residueCardinality χ
          (normalizedAbsoluteValue F.canonicalTopologicalData)
          (unipotentQuotientHaar F.Carrier n) ν.val ρ τ := by
    intro χ ρ τ hρ hτ
    by_cases hr : r = n
    · subst r
      simp only [PairAnalyticInput]
      intro ℓ ℓ' hℓ hℓ'
      exact equalRankAnalytic.{uF, uV, uW} F F.canonicalTopologicalData n
        χ (unipotentQuotientHaar F.Carrier n) hμ V W ρ τ hρ hτ ℓ ℓ' hℓ hℓ'
    · simp only [PairAnalyticInput, dite_eq_right hr]
      intro ℓ ℓ' hℓ hℓ' j k hrank
      subst r
      exact unequalRankAnalytic.{uF, uV, uW} F F.canonicalTopologicalData n j k
        χ (unipotentQuotientHaar F.Carrier n) hμ ν.val V W ρ τ hρ hτ ℓ ℓ' hℓ hℓ'
  have hε : PairEpsilonFactorExists F.canonicalTopologicalData.residueCardinality ψ
      (normalizedAbsoluteValue F.canonicalTopologicalData) ν.val π σ := by
    obtain ⟨ℓ, hℓ⟩ := hπ.exists_ne_zero
    obtain ⟨ℓ', hℓ'⟩ := hσ.exists_ne_zero
    by_cases hr : r = n
    · subst r
      have hFE := equalRankFunctionalEquation.{uF, uV, uW}
        F F.canonicalTopologicalData n ψ
        (unipotentQuotientHaar F.Carrier n) hμ ν.val ν.property
        V W π σ hπ hσ ℓ ℓ' hℓ hℓ'
      obtain ⟨c, m, hcm⟩ := exists_equalRankEpsilonEquation_iff.mpr hFE
      exact ⟨(c, m), isPairEpsilonFactor_self.mpr
        (equalRankEpsilonFactor_of_equation hπ hσ hℓ hℓ' hcm)⟩
    · have hlt : n < r := by omega
      have hFE := unequalRankFunctionalEquation.{uF, uV, uW}
        F F.canonicalTopologicalData n r hlt ψ
        (unipotentQuotientHaar F.Carrier n) hμ ν.val ν.property
        V W π σ hπ hσ ℓ ℓ' hℓ hℓ'
      obtain ⟨c, m, hcm⟩ := exists_unequalRankEpsilonEquation_iff.mpr hFE
      exact ⟨(c, m), (isPairEpsilonFactor_of_lt hlt).mpr
        (unequalRankEpsilonFactor_of_equation hlt hπ hσ hℓ hℓ' hcm)⟩
  exact ⟨hnr, ν.property, hε, hπ, hσ, hA ψ π σ hπ hσ,
    hA (ψ.scale (-1)) (inverseTransposePullback π) (inverseTransposePullback σ)
      (isOfWhittakerType_firstDual ψ π hπ) (isOfWhittakerType_secondDual ψ σ hσ)⟩

/-- Standard Whittaker type of both original representations supplies the
canonical symmetric gamma construction input for every positive rank pair. -/
theorem whittakerTypeGammaConstructionInput :
    WhittakerTypeGammaConstructionInputStatement.{uF, uV, uW} := by
  intro p hp F ψ ν r n V _ _ W _ _ π σ
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  intro hπ hσ
  by_cases hnr : n ≤ r
  · simpa only [PadicSymmetricGammaConstructionInput, ite_eq_left hnr] using
      padicPairGammaConstructionInput_of_whittakerType.{uF, uV, uW}
        F ψ ν r n V W π σ hnr
        hπ ((isOfWhittakerType_standard_iff_inverse ψ σ).mp hσ)
  · simpa only [PadicSymmetricGammaConstructionInput, ite_eq_right hnr] using
      padicPairGammaConstructionInput_of_whittakerType.{uF, uW, uV}
        F ψ ν n r W V σ π (by omega)
        hσ ((isOfWhittakerType_standard_iff_inverse ψ π).mp hπ)

end Langlands.RankinSelberg
