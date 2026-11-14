import Langlands.Representation.RankinSelberg.CanonicalCharacterChange
import Langlands.AllField.Representation.RankinSelberg.CharacterChangeMeasure
import Langlands.AllField.Representation.RankinSelberg.EqualRankCharacterChange
import Langlands.AllField.Representation.RankinSelberg.RectangularCharacterChangeMeasureProof
/-!
# Canonical character change for actual p-adic zeta modules
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding CharacterChangeCompatibleMeasureStatement CharacterChangeRectangularHaarStatement CharacterChangeRectangularProductStatement EqualRankAnalyticStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement UnipotentCharacterChangeModulusStatement characterChangeCompatibleMeasure characterChangeCompatibleMeasure_of_unipotentModulus characterChangeRectangularHaarStatement characterChangeRectangularProductStatement isEqualRankLPolynomial_characterChange_canonical isEqualRankLPolynomial_characterChange_normalized isUnequalRankLPolynomial_characterChange_canonical leviModulus_characterChangeLevi leviModulus_characterChangeLevi_eq_pow normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow unipotentCharacterChangeModulus unipotentQuotientHaar_characterChange unipotentQuotientHaar_sigmaFinite_normalized zetaSpan_equalRank_characterChange_canonical zetaSpan_equalRank_characterChange_normalized zetaSpan_unequalRank_characterChange_canonical
open Langlands.AllField.RankinSelberg

open Langlands.GeneralLinear
open Langlands.Whittaker
open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open _root_.MeasureTheory _root_.Polynomial

universe uF uV uV'

variable {K : Type uF} [Field K] (T : LocalFieldData K)

/-- The actual canonical quotient measure satisfies the character-change law. -/
theorem unipotentQuotientHaar_characterChange (n : ℕ) (a : Kˣ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel (Langlands.GeneralLinear (n + 1) K)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1) K) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1) K)
    letI : BorelSpace (upperUnipotent (n + 1) K) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient n K)
    letI : BorelSpace (LeftUnipotentQuotient n K) := ⟨rfl⟩
    HasCharacterChangeMeasureLaw (normalizedAbsoluteValue T) a
      (unipotentQuotientHaar K n) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel (Langlands.GeneralLinear (n + 1) K)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) K) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) K)
  let : BorelSpace (upperUnipotent (n + 1) K) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n K)
  let : BorelSpace (LeftUnipotentQuotient n K) := ⟨rfl⟩
  exact characterChangeCompatibleMeasure K T n a _
    (unipotentQuotientHaar_isCompatible _ _)

/-- The canonical quotient measure is sigma finite for the supplied p-adic realization. -/
theorem unipotentQuotientHaar_sigmaFinite_normalized (n : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel (Langlands.GeneralLinear (n + 1) K)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1) K) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1) K)
    letI : BorelSpace (upperUnipotent (n + 1) K) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient n K)
    letI : BorelSpace (LeftUnipotentQuotient n K) := ⟨rfl⟩
    SigmaFinite (unipotentQuotientHaar K n) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel (Langlands.GeneralLinear (n + 1) K)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) K) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) K)
  let : BorelSpace (upperUnipotent (n + 1) K) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n K)
  let : BorelSpace (LeftUnipotentQuotient n K) := ⟨rfl⟩
  have : SigmaCompactSpace (Langlands.GeneralLinear (n + 1) K) :=
    T.generalLinearSigmaCompactSpace (n + 1)
  have : SigmaCompactSpace (LeftUnipotentQuotient n K) := by
    apply isSigmaCompact_univ_iff.mp
    rw [← Set.range_eq_univ.mpr (Quotient.mk_surjective (s := QuotientGroup.rightRel
      (upperUnipotent (n + 1) K)))]
    exact isSigmaCompact_range continuous_quot_mk
  infer_instance

/-- The actual p-adic equal-rank Laurent zeta span is unchanged by character scaling. -/
theorem zetaSpan_equalRank_characterChange_canonical (n : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel (Langlands.GeneralLinear (n + 1) K)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1) K) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1) K)
    letI : BorelSpace (upperUnipotent (n + 1) K) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient n K)
    letI : BorelSpace (LeftUnipotentQuotient n K) := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter K) (a : Kˣ)
      (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (V' : Type uV') [AddCommGroup V'] [Module ℂ V']
      (π : Representation ℂ (Langlands.GeneralLinear (n + 1) K) V)
      (π' : Representation ℂ (Langlands.GeneralLinear (n + 1) K) V'),
      zetaSpan (equalRankZetaValues T.residueCardinality ψ (normalizedAbsoluteValue T)
        (unipotentQuotientHaar K n) π π') =
      zetaSpan (equalRankZetaValues T.residueCardinality (ψ.scale a) (normalizedAbsoluteValue T)
        (unipotentQuotientHaar K n) π π') := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel (Langlands.GeneralLinear (n + 1) K)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) K) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) K)
  let : BorelSpace (upperUnipotent (n + 1) K) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n K)
  let : BorelSpace (LeftUnipotentQuotient n K) := ⟨rfl⟩
  intro ψ a V _ _ V' _ _ π π'
  exact zetaSpan_equalRank_characterChange_normalized T n ψ a
    (unipotentQuotientHaar K n) (unipotentQuotientHaar_characterChange T n a)
    V V' π π'

/-- Character scaling preserves each normalized polynomial relation for the actual measures. -/
theorem isEqualRankLPolynomial_characterChange_canonical (n : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel (Langlands.GeneralLinear (n + 1) K)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1) K) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1) K)
    letI : BorelSpace (upperUnipotent (n + 1) K) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient n K)
    letI : BorelSpace (LeftUnipotentQuotient n K) := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter K) (a : Kˣ)
      (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (V' : Type uV') [AddCommGroup V'] [Module ℂ V']
      (π : Representation ℂ (Langlands.GeneralLinear (n + 1) K) V)
      (π' : Representation ℂ (Langlands.GeneralLinear (n + 1) K) V') (P : ℂ[X]),
      IsEqualRankLPolynomial T.residueCardinality ψ (normalizedAbsoluteValue T)
        (unipotentQuotientHaar K n) π π' P ↔
      IsEqualRankLPolynomial T.residueCardinality (ψ.scale a) (normalizedAbsoluteValue T)
        (unipotentQuotientHaar K n) π π' P := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel (Langlands.GeneralLinear (n + 1) K)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) K) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) K)
  let : BorelSpace (upperUnipotent (n + 1) K) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n K)
  let : BorelSpace (LeftUnipotentQuotient n K) := ⟨rfl⟩
  intro ψ a V _ _ V' _ _ π π' P
  exact isNormalizedGenerator_congr
    (zetaSpan_equalRank_characterChange_canonical T n ψ a V V' π π') P

/-- The actual p-adic unequal-rank Laurent zeta span is unchanged by character scaling. -/
theorem zetaSpan_unequalRank_characterChange_canonical (n j k : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel (Langlands.GeneralLinear (n + 1) K)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1) K) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1) K)
    letI : BorelSpace (upperUnipotent (n + 1) K) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient n K)
    letI : BorelSpace (LeftUnipotentQuotient n K) := ⟨rfl⟩
    letI := T.secondCountableTopology
    letI := borel K
    letI : BorelSpace K := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter K) (a : Kˣ)
      (η : AdditiveHaarMeasure K)
      (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (V' : Type uV') [AddCommGroup V'] [Module ℂ V']
      (π : Representation ℂ (Langlands.GeneralLinear (n + (j + k + 1) + 1) K) V)
      (π' : Representation ℂ (Langlands.GeneralLinear (n + 1) K) V'),
      zetaSpan (unequalRankZetaValues T.residueCardinality ψ (normalizedAbsoluteValue T)
        j k (unipotentQuotientHaar K n) (rectangularMeasure η j (n + 1)) π π') =
      zetaSpan (unequalRankZetaValues T.residueCardinality (ψ.scale a) (normalizedAbsoluteValue T)
        j k (unipotentQuotientHaar K n) (rectangularMeasure η j (n + 1)) π π') := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel (Langlands.GeneralLinear (n + 1) K)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) K) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) K)
  let : BorelSpace (upperUnipotent (n + 1) K) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n K)
  let : BorelSpace (LeftUnipotentQuotient n K) := ⟨rfl⟩
  let := T.secondCountableTopology
  let := borel K
  let : BorelSpace K := ⟨rfl⟩
  intro ψ a η V _ _ V' _ _ π π'
  let := T.sigmaCompactSpace
  have : SigmaFinite (unipotentQuotientHaar K n) :=
    unipotentQuotientHaar_sigmaFinite_normalized T n
  exact zetaSpan_unequalRank_characterChange T.residueCardinality
    (Nat.zero_lt_one.trans T.residueCardinality_gt_one) ψ (normalizedAbsoluteValue T)
    a j k (unipotentQuotientHaar K n) (rectangularMeasure η j (n + 1))
    (unipotentQuotientHaar_characterChange T n a)
    (characterChangeRectangularProductStatement K T j n η a)
    (T.ord (Matrix.det (characterChangeElement a n).val))
    (T.normalizedAbs_of_ne_zero (characterChangeElement a n).det_ne_zero) π π'

/-- Character scaling preserves each normalized polynomial relation for the actual measures. -/
theorem isUnequalRankLPolynomial_characterChange_canonical (n j k : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel (Langlands.GeneralLinear (n + 1) K)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1) K) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1) K)
    letI : BorelSpace (upperUnipotent (n + 1) K) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient n K)
    letI : BorelSpace (LeftUnipotentQuotient n K) := ⟨rfl⟩
    letI := T.secondCountableTopology
    letI := borel K
    letI : BorelSpace K := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter K) (a : Kˣ)
      (η : AdditiveHaarMeasure K)
      (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (V' : Type uV') [AddCommGroup V'] [Module ℂ V']
      (π : Representation ℂ (Langlands.GeneralLinear (n + (j + k + 1) + 1) K) V)
      (π' : Representation ℂ (Langlands.GeneralLinear (n + 1) K) V') (P : ℂ[X]),
      IsUnequalRankLPolynomial T.residueCardinality ψ (normalizedAbsoluteValue T)
        j k (unipotentQuotientHaar K n) (rectangularMeasure η j (n + 1)) π π' P ↔
      IsUnequalRankLPolynomial T.residueCardinality (ψ.scale a) (normalizedAbsoluteValue T)
        j k (unipotentQuotientHaar K n) (rectangularMeasure η j (n + 1)) π π' P := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel (Langlands.GeneralLinear (n + 1) K)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) K) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) K)
  let : BorelSpace (upperUnipotent (n + 1) K) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n K)
  let : BorelSpace (LeftUnipotentQuotient n K) := ⟨rfl⟩
  let := T.secondCountableTopology
  let := borel K
  let : BorelSpace K := ⟨rfl⟩
  intro ψ a η V _ _ V' _ _ π π' P
  exact isNormalizedGenerator_congr
    (zetaSpan_unequalRank_characterChange_canonical T n j k ψ a η V V' π π') P

end Langlands.AllField.RankinSelberg
