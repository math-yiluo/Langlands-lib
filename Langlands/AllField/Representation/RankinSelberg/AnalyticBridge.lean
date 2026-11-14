import Langlands.Representation.RankinSelberg.AnalyticBridge
import Langlands.AllField.Representation.RankinSelberg.AnalyticStatementSupplement
/-!
# The JPSS analytic statements and the intrinsic zeta-value sets

For a representation of Whittaker type with a specified nonzero functional, the
intrinsic zeta-value sets of `LocalFactor` coincide with the per-functional rational
values of `AnalyticStatement` once every model integral converges on a right half-plane.
Consequently each analytic conclusion, and each p-adic analytic statement, supplies the
existence proof required by the conditional L-factors. Nothing analytic is proved here.
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

universe uF uV uW

section MultiplicityOne


end MultiplicityOne

section EqualRank



end EqualRank

section UnequalRank



end UnequalRank

section PadicStatements

variable {F : Type uF} [Field F] {T : LocalFieldData F}

/-- The p-adic equal-rank analytic statement supplies, for every pair of Whittaker
type, the existence proof required by `equalRankLFactor`, with the residue cardinality,
the normalized absolute value and any compatible quotient measure. -/
theorem EqualRankAnalyticStatement.normalizedGeneratorExists {n : ℕ}
    (h : EqualRankAnalyticStatement.{uF, uV, uW} F T n) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
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
        ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
        ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W],
        ∀ (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
          (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W),
          IsOfWhittakerType n (standardCharacter ψ n) π →
          IsOfWhittakerType n (inverseStandardCharacter ψ n) σ →
          NormalizedGeneratorExists (equalRankZetaValues T.residueCardinality ψ
            (normalizedAbsoluteValue T) μ π σ) := by
  let _ : TopologicalSpace F := T.topology
  let _ : MeasurableSpace (LeftUnipotentQuotient n F) := borel _
  intro ψ _ μ hμ V _ _ W _ _ π σ hπ hσ
  obtain ⟨ℓ, hℓ⟩ := hπ.exists_ne_zero
  obtain ⟨ℓ', hℓ'⟩ := hσ.exists_ne_zero
  exact (h ψ μ hμ V W π σ hπ hσ ℓ ℓ' hℓ hℓ').normalizedGeneratorExists hπ hσ hℓ hℓ'

end PadicStatements

end Langlands.AllField.RankinSelberg
