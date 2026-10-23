import Langlands.Representation.RankinSelberg.CharacterChangeMeasure
import Langlands.Representation.RankinSelberg.RectangularCharacterChangeMeasureProof
import Langlands.Representation.RankinSelberg.UnequalRankCharacterChange
import Langlands.Group.GL.CountabilityProof

/-!
# Canonical character change for actual p-adic zeta modules
-/

noncomputable section

namespace Langlands.RankinSelberg

open Langlands.GeneralLinear Langlands.Whittaker Langlands.HarmonicAnalysis
open MeasureTheory Polynomial

universe uF uV uV'

variable {p : ℕ} [Fact p.Prime] {K : PadicField.{uF} p} (T : K.TopologicalData)

/-- The actual canonical quotient measure satisfies the character-change law. -/
theorem unipotentQuotientHaar_characterChange (n : ℕ) (a : K.Carrierˣ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel (Langlands.GeneralLinear (n + 1) K.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1) K.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1) K.Carrier)
    letI : BorelSpace (upperUnipotent (n + 1) K.Carrier) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient n K.Carrier)
    letI : BorelSpace (LeftUnipotentQuotient n K.Carrier) := ⟨rfl⟩
    HasCharacterChangeMeasureLaw (normalizedAbsoluteValue T) a
      (unipotentQuotientHaar K.Carrier n) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel (Langlands.GeneralLinear (n + 1) K.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) K.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) K.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) K.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n K.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n K.Carrier) := ⟨rfl⟩
  exact characterChangeCompatibleMeasure p K T n a _
    (unipotentQuotientHaar_isCompatible _ _)

/-- The canonical quotient measure is sigma finite for the supplied p-adic realization. -/
theorem unipotentQuotientHaar_sigmaFinite_normalized (n : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel (Langlands.GeneralLinear (n + 1) K.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1) K.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1) K.Carrier)
    letI : BorelSpace (upperUnipotent (n + 1) K.Carrier) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient n K.Carrier)
    letI : BorelSpace (LeftUnipotentQuotient n K.Carrier) := ⟨rfl⟩
    SigmaFinite (unipotentQuotientHaar K.Carrier n) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel (Langlands.GeneralLinear (n + 1) K.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) K.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) K.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) K.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n K.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n K.Carrier) := ⟨rfl⟩
  have : SigmaCompactSpace (Langlands.GeneralLinear (n + 1) K.Carrier) :=
    T.generalLinearSigmaCompactSpace (n + 1)
  have : SigmaCompactSpace (LeftUnipotentQuotient n K.Carrier) := by
    apply isSigmaCompact_univ_iff.mp
    rw [← Set.range_eq_univ.mpr (Quotient.mk_surjective (s := QuotientGroup.rightRel
      (upperUnipotent (n + 1) K.Carrier)))]
    exact isSigmaCompact_range continuous_quot_mk
  infer_instance

/-- The normalized equal-rank Laurent multiplier with its actual determinant order. -/
def canonicalCharacterChangeLaurentUnit (a : K.Carrierˣ) (n : ℕ) : LaurentCoefficientsˣ :=
  characterChangeLaurentUnit (normalizedAbsoluteValue T) a n
    (T.ord (Matrix.det (characterChangeElement a n).val))

/-- The normalized unequal-rank Laurent multiplier retains the half-gap constant. -/
def canonicalUnequalRankCharacterChangeLaurentUnit (a : K.Carrierˣ) (n j k : ℕ) :
    LaurentCoefficientsˣ :=
  unequalRankCharacterChangeLaurentUnit (normalizedAbsoluteValue T) a n j k
    (T.ord (Matrix.det (characterChangeElement a n).val))

/-- The actual p-adic equal-rank Laurent zeta span is unchanged by character scaling. -/
theorem zetaSpan_equalRank_characterChange_canonical (n : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel (Langlands.GeneralLinear (n + 1) K.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1) K.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1) K.Carrier)
    letI : BorelSpace (upperUnipotent (n + 1) K.Carrier) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient n K.Carrier)
    letI : BorelSpace (LeftUnipotentQuotient n K.Carrier) := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter K.Carrier) (a : K.Carrierˣ)
      (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (V' : Type uV') [AddCommGroup V'] [Module ℂ V']
      (π : Representation ℂ (Langlands.GeneralLinear (n + 1) K.Carrier) V)
      (π' : Representation ℂ (Langlands.GeneralLinear (n + 1) K.Carrier) V'),
      zetaSpan (equalRankZetaValues T.residueCardinality ψ (normalizedAbsoluteValue T)
        (unipotentQuotientHaar K.Carrier n) π π') =
      zetaSpan (equalRankZetaValues T.residueCardinality (ψ.scale a) (normalizedAbsoluteValue T)
        (unipotentQuotientHaar K.Carrier n) π π') := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel (Langlands.GeneralLinear (n + 1) K.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) K.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) K.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) K.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n K.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n K.Carrier) := ⟨rfl⟩
  intro ψ a V _ _ V' _ _ π π'
  exact zetaSpan_equalRank_characterChange_normalized T n ψ a
    (unipotentQuotientHaar K.Carrier n) (unipotentQuotientHaar_characterChange T n a)
    V V' π π'

/-- Character scaling preserves each normalized polynomial relation for the actual measures. -/
theorem isEqualRankLPolynomial_characterChange_canonical (n : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel (Langlands.GeneralLinear (n + 1) K.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1) K.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1) K.Carrier)
    letI : BorelSpace (upperUnipotent (n + 1) K.Carrier) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient n K.Carrier)
    letI : BorelSpace (LeftUnipotentQuotient n K.Carrier) := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter K.Carrier) (a : K.Carrierˣ)
      (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (V' : Type uV') [AddCommGroup V'] [Module ℂ V']
      (π : Representation ℂ (Langlands.GeneralLinear (n + 1) K.Carrier) V)
      (π' : Representation ℂ (Langlands.GeneralLinear (n + 1) K.Carrier) V') (P : ℂ[X]),
      IsEqualRankLPolynomial T.residueCardinality ψ (normalizedAbsoluteValue T)
        (unipotentQuotientHaar K.Carrier n) π π' P ↔
      IsEqualRankLPolynomial T.residueCardinality (ψ.scale a) (normalizedAbsoluteValue T)
        (unipotentQuotientHaar K.Carrier n) π π' P := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel (Langlands.GeneralLinear (n + 1) K.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) K.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) K.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) K.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n K.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n K.Carrier) := ⟨rfl⟩
  intro ψ a V _ _ V' _ _ π π' P
  exact isNormalizedGenerator_congr
    (zetaSpan_equalRank_characterChange_canonical T n ψ a V V' π π') P

/-- Normalized-generator existence and uniqueness transfer for the actual measures. -/
theorem normalizedGeneratorExists_equalRank_characterChange_canonical (n : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel (Langlands.GeneralLinear (n + 1) K.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1) K.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1) K.Carrier)
    letI : BorelSpace (upperUnipotent (n + 1) K.Carrier) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient n K.Carrier)
    letI : BorelSpace (LeftUnipotentQuotient n K.Carrier) := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter K.Carrier) (a : K.Carrierˣ)
      (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (V' : Type uV') [AddCommGroup V'] [Module ℂ V']
      (π : Representation ℂ (Langlands.GeneralLinear (n + 1) K.Carrier) V)
      (π' : Representation ℂ (Langlands.GeneralLinear (n + 1) K.Carrier) V'),
      NormalizedGeneratorExists (equalRankZetaValues T.residueCardinality ψ (normalizedAbsoluteValue T)
        (unipotentQuotientHaar K.Carrier n) π π') ↔
      NormalizedGeneratorExists (equalRankZetaValues T.residueCardinality (ψ.scale a) (normalizedAbsoluteValue T)
        (unipotentQuotientHaar K.Carrier n) π π') := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel (Langlands.GeneralLinear (n + 1) K.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) K.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) K.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) K.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n K.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n K.Carrier) := ⟨rfl⟩
  intro ψ a V _ _ V' _ _ π π'
  exact normalizedGeneratorExists_congr
    (zetaSpan_equalRank_characterChange_canonical T n ψ a V V' π π')

/-- The actual p-adic unequal-rank Laurent zeta span is unchanged by character scaling. -/
theorem zetaSpan_unequalRank_characterChange_canonical (n j k : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel (Langlands.GeneralLinear (n + 1) K.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1) K.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1) K.Carrier)
    letI : BorelSpace (upperUnipotent (n + 1) K.Carrier) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient n K.Carrier)
    letI : BorelSpace (LeftUnipotentQuotient n K.Carrier) := ⟨rfl⟩
    letI := T.secondCountableTopology
    letI := borel K.Carrier
    letI : BorelSpace K.Carrier := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter K.Carrier) (a : K.Carrierˣ)
      (η : AdditiveHaarMeasure K.Carrier)
      (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (V' : Type uV') [AddCommGroup V'] [Module ℂ V']
      (π : Representation ℂ (Langlands.GeneralLinear (n + (j + k + 1) + 1) K.Carrier) V)
      (π' : Representation ℂ (Langlands.GeneralLinear (n + 1) K.Carrier) V'),
      zetaSpan (unequalRankZetaValues T.residueCardinality ψ (normalizedAbsoluteValue T)
        j k (unipotentQuotientHaar K.Carrier n) (rectangularMeasure η j (n + 1)) π π') =
      zetaSpan (unequalRankZetaValues T.residueCardinality (ψ.scale a) (normalizedAbsoluteValue T)
        j k (unipotentQuotientHaar K.Carrier n) (rectangularMeasure η j (n + 1)) π π') := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel (Langlands.GeneralLinear (n + 1) K.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) K.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) K.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) K.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n K.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n K.Carrier) := ⟨rfl⟩
  let := T.secondCountableTopology
  let := borel K.Carrier
  let : BorelSpace K.Carrier := ⟨rfl⟩
  intro ψ a η V _ _ V' _ _ π π'
  let := T.sigmaCompactSpace
  have : SigmaFinite (unipotentQuotientHaar K.Carrier n) :=
    unipotentQuotientHaar_sigmaFinite_normalized T n
  exact zetaSpan_unequalRank_characterChange T.residueCardinality
    (Nat.zero_lt_one.trans T.residueCardinality_gt_one) ψ (normalizedAbsoluteValue T)
    a j k (unipotentQuotientHaar K.Carrier n) (rectangularMeasure η j (n + 1))
    (unipotentQuotientHaar_characterChange T n a)
    (characterChangeRectangularProductStatement p K T j n η a)
    (T.ord (Matrix.det (characterChangeElement a n).val))
    (T.normalizedAbs_of_ne_zero (characterChangeElement a n).det_ne_zero) π π'

/-- Character scaling preserves each normalized polynomial relation for the actual measures. -/
theorem isUnequalRankLPolynomial_characterChange_canonical (n j k : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel (Langlands.GeneralLinear (n + 1) K.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1) K.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1) K.Carrier)
    letI : BorelSpace (upperUnipotent (n + 1) K.Carrier) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient n K.Carrier)
    letI : BorelSpace (LeftUnipotentQuotient n K.Carrier) := ⟨rfl⟩
    letI := T.secondCountableTopology
    letI := borel K.Carrier
    letI : BorelSpace K.Carrier := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter K.Carrier) (a : K.Carrierˣ)
      (η : AdditiveHaarMeasure K.Carrier)
      (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (V' : Type uV') [AddCommGroup V'] [Module ℂ V']
      (π : Representation ℂ (Langlands.GeneralLinear (n + (j + k + 1) + 1) K.Carrier) V)
      (π' : Representation ℂ (Langlands.GeneralLinear (n + 1) K.Carrier) V') (P : ℂ[X]),
      IsUnequalRankLPolynomial T.residueCardinality ψ (normalizedAbsoluteValue T)
        j k (unipotentQuotientHaar K.Carrier n) (rectangularMeasure η j (n + 1)) π π' P ↔
      IsUnequalRankLPolynomial T.residueCardinality (ψ.scale a) (normalizedAbsoluteValue T)
        j k (unipotentQuotientHaar K.Carrier n) (rectangularMeasure η j (n + 1)) π π' P := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel (Langlands.GeneralLinear (n + 1) K.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) K.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) K.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) K.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n K.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n K.Carrier) := ⟨rfl⟩
  let := T.secondCountableTopology
  let := borel K.Carrier
  let : BorelSpace K.Carrier := ⟨rfl⟩
  intro ψ a η V _ _ V' _ _ π π' P
  exact isNormalizedGenerator_congr
    (zetaSpan_unequalRank_characterChange_canonical T n j k ψ a η V V' π π') P

/-- Normalized-generator existence and uniqueness transfer for the actual measures. -/
theorem normalizedGeneratorExists_unequalRank_characterChange_canonical (n j k : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel (Langlands.GeneralLinear (n + 1) K.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1) K.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1) K.Carrier)
    letI : BorelSpace (upperUnipotent (n + 1) K.Carrier) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient n K.Carrier)
    letI : BorelSpace (LeftUnipotentQuotient n K.Carrier) := ⟨rfl⟩
    letI := T.secondCountableTopology
    letI := borel K.Carrier
    letI : BorelSpace K.Carrier := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter K.Carrier) (a : K.Carrierˣ)
      (η : AdditiveHaarMeasure K.Carrier)
      (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (V' : Type uV') [AddCommGroup V'] [Module ℂ V']
      (π : Representation ℂ (Langlands.GeneralLinear (n + (j + k + 1) + 1) K.Carrier) V)
      (π' : Representation ℂ (Langlands.GeneralLinear (n + 1) K.Carrier) V'),
      NormalizedGeneratorExists (unequalRankZetaValues T.residueCardinality ψ (normalizedAbsoluteValue T)
        j k (unipotentQuotientHaar K.Carrier n) (rectangularMeasure η j (n + 1)) π π') ↔
      NormalizedGeneratorExists (unequalRankZetaValues T.residueCardinality (ψ.scale a) (normalizedAbsoluteValue T)
        j k (unipotentQuotientHaar K.Carrier n) (rectangularMeasure η j (n + 1)) π π') := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel (Langlands.GeneralLinear (n + 1) K.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) K.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) K.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) K.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n K.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n K.Carrier) := ⟨rfl⟩
  let := T.secondCountableTopology
  let := borel K.Carrier
  let : BorelSpace K.Carrier := ⟨rfl⟩
  intro ψ a η V _ _ V' _ _ π π'
  exact normalizedGeneratorExists_congr
    (zetaSpan_unequalRank_characterChange_canonical T n j k ψ a η V V' π π')

end Langlands.RankinSelberg
