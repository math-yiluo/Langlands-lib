import Langlands.Representation.RankinSelberg.EqualRankCharacterChange
import Langlands.AllField.Representation.RankinSelberg.AnalyticStatementSupplement
/-!
# Rational equal-rank zeta transport under change of additive character

The actual integral multiplier is a Laurent unit when the determinant absolute
value is an integer power of q. The quotient measure law remains explicit.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement isEqualRankLPolynomial_characterChange_normalized normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open Langlands.GeneralLinear
open Langlands.Whittaker
open Langlands.HarmonicAnalysis
open _root_.MeasureTheory _root_.Polynomial

universe uF uV uV'

variable {F : Type uF} [Field F]

section EqualRank




end EqualRank

section Padic

variable {K : Type uF} [Field K] (T : LocalFieldData K)

/-- The shared p-adic normalization supplies the determinant-order exponent. -/
theorem normalizedDeterminantWeight_eq_spectralPoint_zpow {m : ℕ}
    (g : Langlands.GeneralLinear m K) (s : ℂ) :
    determinantWeight (normalizedAbsoluteValue T) g s =
      spectralPoint T.residueCardinality s ^ T.ord (Matrix.det g.val) :=
  determinantWeight_eq_spectralPoint_zpow T.residueCardinality
    (Nat.zero_lt_one.trans T.residueCardinality_gt_one) (normalizedAbsoluteValue T)
    g (T.ord (Matrix.det g.val)) (T.normalizedAbs_of_ne_zero g.det_ne_zero) s

/-- P-adic equal-rank span invariance needs only the explicit measure transport
law; its numerical determinant normalization is discharged internally. -/
theorem zetaSpan_equalRank_characterChange_normalized (n : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel (LeftUnipotentQuotient n K)
    letI : BorelSpace (LeftUnipotentQuotient n K) := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter K) (a : Kˣ)
      (μ : Measure (LeftUnipotentQuotient n K)),
      HasCharacterChangeMeasureLaw (normalizedAbsoluteValue T) a μ →
      ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
        (V' : Type uV') [AddCommGroup V'] [Module ℂ V']
        (π : Representation ℂ (Langlands.GeneralLinear (n + 1) K) V)
        (π' : Representation ℂ (Langlands.GeneralLinear (n + 1) K) V'),
        zetaSpan (equalRankZetaValues T.residueCardinality ψ
          (normalizedAbsoluteValue T) μ π π') =
        zetaSpan (equalRankZetaValues T.residueCardinality (ψ.scale a)
          (normalizedAbsoluteValue T) μ π π') := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel (LeftUnipotentQuotient n K)
  let : BorelSpace (LeftUnipotentQuotient n K) := ⟨rfl⟩
  intro ψ a μ hμ V _ _ V' _ _ π π'
  exact zetaSpan_equalRank_characterChange T.residueCardinality
    (Nat.zero_lt_one.trans T.residueCardinality_gt_one) ψ (normalizedAbsoluteValue T)
    a μ hμ (T.ord (Matrix.det (characterChangeElement a n).val))
    (T.normalizedAbs_of_ne_zero (characterChangeElement a n).det_ne_zero) π π'

/-- Under the same measure law, the p-adic normalized L-polynomial relation is
unchanged by scaling the additive character. No generator existence is assumed. -/
theorem isEqualRankLPolynomial_characterChange_normalized (n : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel (LeftUnipotentQuotient n K)
    letI : BorelSpace (LeftUnipotentQuotient n K) := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter K) (a : Kˣ)
      (μ : Measure (LeftUnipotentQuotient n K)),
      HasCharacterChangeMeasureLaw (normalizedAbsoluteValue T) a μ →
      ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
        (V' : Type uV') [AddCommGroup V'] [Module ℂ V']
        (π : Representation ℂ (Langlands.GeneralLinear (n + 1) K) V)
        (π' : Representation ℂ (Langlands.GeneralLinear (n + 1) K) V') (P : ℂ[X]),
        IsEqualRankLPolynomial T.residueCardinality ψ (normalizedAbsoluteValue T) μ π π' P ↔
        IsEqualRankLPolynomial T.residueCardinality (ψ.scale a)
          (normalizedAbsoluteValue T) μ π π' P := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel (LeftUnipotentQuotient n K)
  let : BorelSpace (LeftUnipotentQuotient n K) := ⟨rfl⟩
  intro ψ a μ hμ V _ _ V' _ _ π π' P
  exact isNormalizedGenerator_congr
    (zetaSpan_equalRank_characterChange_normalized T n ψ a μ hμ V V' π π') P

end Padic

end Langlands.AllField.RankinSelberg
