import Langlands.Representation.RankinSelberg.AnalyticStatement

/-!
# Equal-rank integrals with a last-row orbit cutoff

JPSS (1983), printed 449, displays (1) and (3): an equal-rank integral whose
Schwartz variable is the indicator of the last-row orbit of a small compact
open subgroup reduces to the corank-one integral of the restrictions to
`diag(h, 1)`. This module only defines the proposition.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

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
  letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  letI := borel (upperUnipotent (n + 1) F.Carrier)
  letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  letI := borel (LeftUnipotentQuotient n F.Carrier)
  letI : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  letI := borel (Langlands.GeneralLinear (n + 1 + 1) F.Carrier)
  letI : BorelSpace (Langlands.GeneralLinear (n + 1 + 1) F.Carrier) := ⟨rfl⟩
  letI := borel (upperUnipotent (n + 1 + 1) F.Carrier)
  letI : BorelSpace (upperUnipotent (n + 1 + 1) F.Carrier) := ⟨rfl⟩
  letI := borel (LeftUnipotentQuotient (n + 1) F.Carrier)
  letI : BorelSpace (LeftUnipotentQuotient (n + 1) F.Carrier) := ⟨rfl⟩
  ∀ [Measure.IsMulRightInvariant (unipotentHaar F.Carrier n)],
  ∀ [Measure.IsMulRightInvariant (unipotentHaar F.Carrier (n + 1))],
  ∀ (μ : Measure (LeftUnipotentQuotient (n + 1) F.Carrier))
    (μ' : Measure (LeftUnipotentQuotient n F.Carrier)),
    IsCompatible (upperUnipotent (n + 1 + 1) F.Carrier)
      (generalLinearHaar F.Carrier (n + 1)) (unipotentHaar F.Carrier (n + 1)) μ →
    IsCompatible (upperUnipotent (n + 1) F.Carrier)
      (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n) μ' →
    ∀ J : OpenSubgroup (Langlands.GeneralLinear (n + 1 + 1) F.Carrier),
      IsCompact (J : Set (Langlands.GeneralLinear (n + 1 + 1) F.Carrier)) →
      ∃ c : ℝ, 0 < c ∧
        ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
          (W : WhittakerFunctions ψ (n + 1)) (W' : InverseWhittakerFunctions ψ (n + 1))
          (W'' : InverseWhittakerFunctions ψ n)
          (Φ : SchwartzBruhat (Fin (n + 1 + 1) → F.Carrier)),
          (∀ (g : Langlands.GeneralLinear (n + 1 + 1) F.Carrier) (j : J),
            W.val (g * j.val) = W.val g) →
          (∀ (g : Langlands.GeneralLinear (n + 1 + 1) F.Carrier) (j : J),
            W'.val (g * j.val) = W'.val g) →
          (∀ h : Langlands.GeneralLinear (n + 1) F.Carrier,
            W''.val h = W'.val (rankInclusion 1 h)) →
          (Φ : (Fin (n + 1 + 1) → F.Carrier) → ℂ) =
            (lastRow '' (J : Set (Langlands.GeneralLinear (n + 1 + 1) F.Carrier))).indicator
              (fun _ => (1 : ℂ)) →
          ∀ s : ℂ,
            (EqualRankConverges ψ (normalizedAbsoluteValue T) μ W W' Φ s ↔
              CorankOneConverges ψ (normalizedAbsoluteValue T) μ' W W'' (s - 1 / 2)) ∧
            equalRankIntegral ψ (normalizedAbsoluteValue T) μ W W' Φ s =
              (c : ℂ) * corankOneIntegral ψ (normalizedAbsoluteValue T) μ' W W'' (s - 1 / 2)

end Langlands.RankinSelberg
