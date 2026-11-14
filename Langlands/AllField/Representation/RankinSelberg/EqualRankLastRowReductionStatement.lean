import Langlands.Representation.RankinSelberg.EqualRankLastRowReductionStatement
import Langlands.AllField.Representation.RankinSelberg.AnalyticStatementSupplement
/-!
# Equal-rank integrals with a last-row orbit cutoff

JPSS (1983), printed 449, displays (1) and (3): an equal-rank integral whose
Schwartz variable is the indicator of the last-row orbit of a small compact
open subgroup reduces to the corank-one integral of the restrictions to
`diag(h, 1)`. This module only defines the proposition.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankLastRowReductionStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis
open Langlands.Whittaker
open Langlands.GeneralLinear
open Langlands.QuotientIntegration

universe uF

variable (F : Type uF) [Field F] (T : LocalFieldData F)

/-- For compatible quotient measures in ranks `n + 2` and `n + 1` and a compact
open subgroup `J` of `GL_(n+2)`, there is one positive constant `c` such that,
for all right `J`-invariant `W, W'`, the restriction `W''` of `W'` to
`diag(h, 1)`, and the exact indicator `Φ` of the last-row orbit of `J`, the
equal-rank integral converges exactly when the corank-one integral at `s - 1/2`
does, and then equals `c` times it. -/
def EqualRankLastRowReductionStatement (n : ℕ) : Prop :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := borel (Langlands.GeneralLinear (n + 1) F)
  letI : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
  letI := borel (upperUnipotent (n + 1) F)
  letI : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
  letI := borel (LeftUnipotentQuotient n F)
  letI : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
  letI := borel (Langlands.GeneralLinear (n + 1 + 1) F)
  letI : BorelSpace (Langlands.GeneralLinear (n + 1 + 1) F) := ⟨rfl⟩
  letI := borel (upperUnipotent (n + 1 + 1) F)
  letI : BorelSpace (upperUnipotent (n + 1 + 1) F) := ⟨rfl⟩
  letI := borel (LeftUnipotentQuotient (n + 1) F)
  letI : BorelSpace (LeftUnipotentQuotient (n + 1) F) := ⟨rfl⟩
  ∀ [Measure.IsMulRightInvariant (unipotentHaar F n)],
  ∀ [Measure.IsMulRightInvariant (unipotentHaar F (n + 1))],
  ∀ (μ : Measure (LeftUnipotentQuotient (n + 1) F))
    (μ' : Measure (LeftUnipotentQuotient n F)),
    IsCompatible (upperUnipotent (n + 1 + 1) F)
      (generalLinearHaar F (n + 1)) (unipotentHaar F (n + 1)) μ →
    IsCompatible (upperUnipotent (n + 1) F)
      (generalLinearHaar F n) (unipotentHaar F n) μ' →
    ∀ J : OpenSubgroup (Langlands.GeneralLinear (n + 1 + 1) F),
      IsCompact (J : Set (Langlands.GeneralLinear (n + 1 + 1) F)) →
      ∃ c : ℝ, 0 < c ∧
        ∀ (ψ : UnitaryAdditiveCharacter F)
          (W : WhittakerFunctions ψ (n + 1)) (W' : InverseWhittakerFunctions ψ (n + 1))
          (W'' : InverseWhittakerFunctions ψ n)
          (Φ : SchwartzBruhat (Fin (n + 1 + 1) → F)),
          (∀ (g : Langlands.GeneralLinear (n + 1 + 1) F) (j : J),
            W.val (g * j.val) = W.val g) →
          (∀ (g : Langlands.GeneralLinear (n + 1 + 1) F) (j : J),
            W'.val (g * j.val) = W'.val g) →
          (∀ h : Langlands.GeneralLinear (n + 1) F,
            W''.val h = W'.val (rankInclusion 1 h)) →
          (Φ : (Fin (n + 1 + 1) → F) → ℂ) =
            (lastRow '' (J : Set (Langlands.GeneralLinear (n + 1 + 1) F))).indicator
              (fun _ => (1 : ℂ)) →
          ∀ s : ℂ,
            (EqualRankConverges ψ (normalizedAbsoluteValue T) μ W W' Φ s ↔
              CorankOneConverges ψ (normalizedAbsoluteValue T) μ' W W'' (s - 1 / 2)) ∧
            equalRankIntegral ψ (normalizedAbsoluteValue T) μ W W' Φ s =
              (c : ℂ) * corankOneIntegral ψ (normalizedAbsoluteValue T) μ' W W'' (s - 1 / 2)

end Langlands.AllField.RankinSelberg
