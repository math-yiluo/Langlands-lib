import Langlands.Representation.RankinSelberg.PairLFactor
import Langlands.AllField.Representation.RankinSelberg.AnalyticBridge
/-!
# The L-factor of a pair

For `π` on `GL_(r+1)` and `σ` on `GL_(n+1)` with `n ≤ r`, the L-polynomial of the pair
is the normalized generator of the equal-rank zeta values when `r = n`, and the common
normalized generator of the zeta values of every rectangular block when `n < r`
(JPSS Theorem 2.7(ii)). The L-factor is constructed only from a proof that this
polynomial exists. The relation is invariant under equivalences and determinant
twists, the dual pair uses the inverse-transpose pullbacks and `ψ⁻¹`, and the p-adic
analytic statements supply the existence proof for pairs of Whittaker type.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory _root_.Polynomial
open Langlands.QuotientIntegration
open Langlands.GeneralLinear
open Langlands.Whittaker
open Langlands.HarmonicAnalysis

universe uF uV uW uV₂ uW₂

section Surjections


end Surjections

section WhittakerSets


end WhittakerSets

section ZetaValueTransport



end ZetaValueTransport

section FixedRanks



end FixedRanks

section PairRelation

variable {F : Type uF} [Field F] [TopologicalSpace F] [MeasurableSpace F]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {V₂ : Type uV₂} [AddCommGroup V₂] [Module ℂ V₂]
  {W₂ : Type uW₂} [AddCommGroup W₂] [Module ℂ W₂]
  {n r : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)]

variable {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ}
  {μ : Measure (LeftUnipotentQuotient n F)} {ν : AdditiveHaarMeasure F}
  {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}
  {P P' : ℂ[X]}

section EqualRank


end EqualRank

section UnequalRank


end UnequalRank

section Invariance

end Invariance

end PairRelation

section DualPair



end DualPair

section PadicStatements

variable {F : Type uF} [Field F] {T : LocalFieldData F}

/-- The p-adic equal-rank analytic statement supplies the L-polynomial of every
equal-rank pair of Whittaker type, for every compatible quotient measure. -/
theorem EqualRankAnalyticStatement.pairLPolynomialExists {n : ℕ}
    (h : EqualRankAnalyticStatement.{uF, uV, uW} F T n) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel F
    letI := borel (Langlands.GeneralLinear (n + 1) F)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1) F)
    letI : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient n F)
    letI : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
    ∀ ψ : UnitaryAdditiveCharacter F,
      ∀ [Measure.IsMulRightInvariant (unipotentHaar F n)],
      ∀ μ : Measure (LeftUnipotentQuotient n F),
        IsCompatible (upperUnipotent (n + 1) F)
          (generalLinearHaar F n) (unipotentHaar F n) μ →
        ∀ ν : AdditiveHaarMeasure F,
        ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
        ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W],
        ∀ (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
          (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W),
          IsOfWhittakerType n (standardCharacter ψ n) π →
          IsOfWhittakerType n (inverseStandardCharacter ψ n) σ →
          PairLPolynomialExists T.residueCardinality ψ (normalizedAbsoluteValue T) μ ν π σ := by
  let _ : TopologicalSpace F := T.topology
  let _ : MeasurableSpace (LeftUnipotentQuotient n F) := borel _
  let _ : MeasurableSpace F := borel _
  intro ψ _ μ hμ ν V _ _ W _ _ π σ hπ hσ
  exact pairLPolynomialExists_self_iff.2
    (h.normalizedGeneratorExists ψ μ hμ V W π σ hπ hσ)

/-- The p-adic unequal-rank analytic statements of every block, together with the
common-generator statement, supply the L-polynomial of every unequal-rank pair of
Whittaker type. -/
theorem UnequalRankCommonGeneratorStatement.pairLPolynomialExists {n r : ℕ}
    (hC : UnequalRankCommonGeneratorStatement.{uF, uV, uW} F T n r)
    (hU : ∀ j k : ℕ, r = n + (j + k + 1) →
      UnequalRankAnalyticStatement.{uF, uV, uW} F T n j k) (hnr : n < r) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel F
    letI := borel (Langlands.GeneralLinear (n + 1) F)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1) F)
    letI : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient n F)
    letI : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
    ∀ ψ : UnitaryAdditiveCharacter F,
      ∀ [Measure.IsMulRightInvariant (unipotentHaar F n)],
      ∀ μ : Measure (LeftUnipotentQuotient n F),
        IsCompatible (upperUnipotent (n + 1) F)
          (generalLinearHaar F n) (unipotentHaar F n) μ →
        ∀ ν : AdditiveHaarMeasure F,
        ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
        ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W],
        ∀ (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
          (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W),
          IsOfWhittakerType r (standardCharacter ψ r) π →
          IsOfWhittakerType n (inverseStandardCharacter ψ n) σ →
          PairLPolynomialExists T.residueCardinality ψ (normalizedAbsoluteValue T) μ ν π σ := by
  let _ : TopologicalSpace F := T.topology
  let _ : MeasurableSpace (LeftUnipotentQuotient n F) := borel _
  let _ : MeasurableSpace F := borel _
  intro ψ _ μ hμ ν V _ _ W _ _ π σ hπ hσ
  obtain ⟨ℓ, hℓ⟩ := hπ.exists_ne_zero
  obtain ⟨ℓ', hℓ'⟩ := hσ.exists_ne_zero
  obtain ⟨P, hP⟩ := hC hnr ψ μ hμ ν V W π σ hπ hσ ℓ ℓ' hℓ hℓ'
  refine ⟨P, (isPairLPolynomial_of_lt hnr).2 fun j k hr => ?_⟩
  have hPj := hP j k hr
  subst hr
  rw [unequalRankZetaValuesAt_rfl,
    (hU j k rfl ψ μ hμ ν V W π σ hπ hσ ℓ ℓ' hℓ hℓ').zetaValues_eq hπ hσ hℓ hℓ']
  exact hPj

end PadicStatements

end Langlands.AllField.RankinSelberg
