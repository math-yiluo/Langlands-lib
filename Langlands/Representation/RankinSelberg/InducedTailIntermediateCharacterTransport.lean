import Langlands.Representation.RankinSelberg.CanonicalCharacterChange
import Langlands.Representation.RankinSelberg.EqualRankSwapTransport
import Langlands.Representation.RankinSelberg.PairLFactor

/-! # Inverse-character transport for the intermediate tail comparison -/

noncomputable section

namespace Langlands.RankinSelberg

open GeneralLinear Whittaker HarmonicAnalysis MeasureTheory

universe uF uV uW

section Algebra

variable {F : Type uF} [Field F]

/-- The character-change diagonal at `-1` has determinant of absolute value one. -/
theorem characterChangeElement_neg_one_abs_det (abv : AbsoluteValue F ℝ) (n : ℕ) :
    abv (Matrix.det (characterChangeElement (-1 : Fˣ) n).val) = 1 := by
  simp [characterChangeElement, Matrix.det_diagonal, map_prod, map_pow]

/-- The rectangular character-change modulus is one at `-1`. -/
theorem characterChangeRectangularModulus_neg_one
    (abv : AbsoluteValue F ℝ) (j n : ℕ) :
    characterChangeRectangularModulus abv (-1 : Fˣ) j n = 1 := by
  apply NNReal.eq
  change abv (-1 : F) ^ characterChangeRectangularExponent j n = 1
  simp

/-- Both measure moduli and the determinant half-gap are trivial at `-1`. -/
theorem unequalRankCharacterChangeScalar_neg_one (abv : AbsoluteValue F ℝ) (n j k : ℕ) :
    unequalRankCharacterChangeScalar abv (-1 : Fˣ) n j k = 1 := by
  apply Units.ext
  simp [unequalRankCharacterChangeScalar_val, characterChangeModulus_neg_one,
    characterChangeRectangularModulus_neg_one, determinantWeight]

variable [TopologicalSpace F] [IsTopologicalRing F]

/-- Scaling by `-1` is the pointwise inverse additive character. -/
theorem scaled_neg_one_apply (ψ : UnitaryAdditiveCharacter F) (x : F) :
    ψ.scale (-1 : Fˣ) x = (ψ x)⁻¹ := by
  simpa only [UnitaryAdditiveCharacter.scale_apply, Units.val_neg, Units.val_one,
    neg_one_mul] using AddChar.map_neg_eq_inv ψ.toAddChar x

end Algebra

section Conditional

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
variable (q : ℕ) (hq : 0 < q) (ψ : UnitaryAdditiveCharacter F)
variable (abv : AbsoluteValue F ℝ) {n : ℕ} (j k : ℕ)
variable [MeasurableSpace (LeftUnipotentQuotient n F)]
variable [BorelSpace (LeftUnipotentQuotient n F)]
variable [MeasurableSpace (Matrix (Fin j) (Fin (n + 1)) F)]
variable [BorelSpace (Matrix (Fin j) (Fin (n + 1)) F)]
variable (μ : Measure (LeftUnipotentQuotient n F))
variable (η : Measure (Matrix (Fin j) (Fin (n + 1)) F))
variable (hμ : HasCharacterChangeMeasureLaw abv (-1 : Fˣ) μ)
variable (hη : HasCharacterChangeRectangularMeasureLaw abv (-1 : Fˣ) j n η)

include hμ hη

/-- The corrected coefficient functions have exactly the original integral
under inverse-character transport; no Laurent multiplier remains. -/
theorem unequalRankIntegral_scale_neg_one
    (W : WhittakerFunctions ψ (n + (j + k + 1)))
    (W' : InverseWhittakerFunctions ψ n) (s : ℂ) :
    unequalRankIntegral (ψ.scale (-1 : Fˣ)) abv j k μ η
      (unequalRankCharacterChangeFunction ψ (-1 : Fˣ) n j k W)
      (characterChangeInverseFunction ψ n (-1 : Fˣ) W') s =
      unequalRankIntegral ψ abv j k μ η W W' s := by
  simpa [determinantWeight, characterChangeElement_neg_one_abs_det,
    characterChangeModulus_neg_one, characterChangeRectangularModulus_neg_one] using
      unequalRankIntegral_characterChange abv (-1 : Fˣ) j n μ η ψ k hμ hη W W' s

variable [SFinite μ] [SFinite η]

/-- The same corrected coefficient functions preserve absolute convergence. -/
theorem unequalRankConverges_scale_neg_one_iff
    (W : WhittakerFunctions ψ (n + (j + k + 1)))
    (W' : InverseWhittakerFunctions ψ n) (s : ℂ) :
    UnequalRankConverges (ψ.scale (-1 : Fˣ)) abv j k μ η
      (unequalRankCharacterChangeFunction ψ (-1 : Fˣ) n j k W)
      (characterChangeInverseFunction ψ n (-1 : Fˣ) W') s ↔
      UnequalRankConverges ψ abv j k μ η W W' s :=
  unequalRankConverges_characterChange_iff abv (-1 : Fˣ) j n μ η ψ k hμ hη W W' s

omit [SFinite μ] [SFinite η] in
/-- The actual continuation is unchanged, with its rational function retained. -/
theorem unequalRankContinuation_scale_neg_one_iff
    (W : WhittakerFunctions ψ (n + (j + k + 1)))
    (W' : InverseWhittakerFunctions ψ n) (R : RationalFunctions) :
    HasRationalContinuation q
      (unequalRankIntegral (ψ.scale (-1 : Fˣ)) abv j k μ η
        (unequalRankCharacterChangeFunction ψ (-1 : Fˣ) n j k W)
        (characterChangeInverseFunction ψ n (-1 : Fˣ) W')) R ↔
      HasRationalContinuation q (unequalRankIntegral ψ abv j k μ η W W') R := by
  have hi :
      unequalRankIntegral (ψ.scale (-1 : Fˣ)) abv j k μ η
          (unequalRankCharacterChangeFunction ψ (-1 : Fˣ) n j k W)
          (characterChangeInverseFunction ψ n (-1 : Fˣ) W') =
        unequalRankIntegral ψ abv j k μ η W W' := by
    funext s
    exact unequalRankIntegral_scale_neg_one ψ abv j k μ η hμ hη W W' s
  rw [hi]

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable (π : Representation ℂ (Langlands.GeneralLinear (n + (j + k + 1) + 1) F) V)
variable (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)

include hq

/-- Inverse-character change preserves the actual rational-value set, including
coefficient, convergence and continuation witnesses. -/
theorem unequalRankZetaValues_scale_neg_one :
    unequalRankZetaValues q ψ abv j k μ η π σ =
      unequalRankZetaValues q (ψ.scale (-1 : Fˣ)) abv j k μ η π σ := by
  have he : abv (Matrix.det (characterChangeElement (-1 : Fˣ) n).val) =
      (q : ℝ) ^ (-(0 : ℤ)) := by
    simp
  ext R
  constructor
  · intro hR
    simpa only [unequalRankCharacterChangeScalar_neg_one, Units.val_one,
      neg_zero, zpow_zero, map_one, one_mul] using
        unequalRankZetaValues_characterChange q hq ψ abv (-1 : Fˣ) j k μ η
          hμ hη 0 he π σ hR
  · intro hR
    simpa only [unequalRankCharacterChangeScalar_neg_one, inv_one, Units.val_one,
      zpow_zero, map_one, one_mul] using
        unequalRankZetaValues_characterChange_reverse q hq ψ abv (-1 : Fˣ) j k μ η
          hμ hη 0 he π σ hR

end Conditional

section Compatible

variable {p : ℕ} [Fact p.Prime] {K : PadicField.{uF} p} (T : K.TopologicalData)

/-- With the supplied p-adic topology, arbitrary compatible quotient measures
and the rectangular Haar measure give the same actual values at inverse character.
The two quotient measures may be supplied independently. -/
theorem unequalRankZetaValues_scale_neg_one_compatible (n j k : ℕ) :
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
    ∀ (ψ : UnitaryAdditiveCharacter K.Carrier)
      (η : AdditiveHaarMeasure K.Carrier)
      (μ μinv : Measure (LeftUnipotentQuotient n K.Carrier)),
      QuotientIntegration.IsCompatible (upperUnipotent (n + 1) K.Carrier)
        (generalLinearHaar K.Carrier n) (unipotentHaar K.Carrier n) μ →
      QuotientIntegration.IsCompatible (upperUnipotent (n + 1) K.Carrier)
        (generalLinearHaar K.Carrier n) (unipotentHaar K.Carrier n) μinv →
      ∀ {V : Type uV} [AddCommGroup V] [Module ℂ V]
        {W : Type uW} [AddCommGroup W] [Module ℂ W]
        (π : Representation ℂ
          (Langlands.GeneralLinear (n + (j + k + 1) + 1) K.Carrier) V)
        (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) K.Carrier) W),
        unequalRankZetaValues T.residueCardinality ψ (normalizedAbsoluteValue T)
          j k μ (rectangularMeasure η j (n + 1)) π σ =
        unequalRankZetaValues T.residueCardinality (ψ.scale (-1 : K.Carrierˣ))
          (normalizedAbsoluteValue T) j k μinv (rectangularMeasure η j (n + 1)) π σ := by
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
  intro ψ η μ μinv hμ hμinv V _ _ W _ _ π σ
  rw [unipotentQuotientHaar_unique K.Carrier n μ hμ,
    unipotentQuotientHaar_unique K.Carrier n μinv hμinv]
  let := T.sigmaCompactSpace
  have : SigmaFinite (unipotentQuotientHaar K.Carrier n) :=
    unipotentQuotientHaar_sigmaFinite_normalized T n
  exact unequalRankZetaValues_scale_neg_one T.residueCardinality
    (Nat.zero_lt_one.trans T.residueCardinality_gt_one) ψ (normalizedAbsoluteValue T)
    j k (unipotentQuotientHaar K.Carrier n) (rectangularMeasure η j (n + 1))
    (unipotentQuotientHaar_characterChange T n (-1))
    (characterChangeRectangularProductStatement p K T j n η (-1)) π σ

/-- The compatible-measure equality also respects an independently fixed large rank.
In particular it applies to the larger-first tail pair in the intermediate case. -/
theorem unequalRankZetaValuesAt_scale_neg_one_compatible (n r j k : ℕ)
    (hr : r = n + (j + k + 1)) :
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
    ∀ (ψ : UnitaryAdditiveCharacter K.Carrier)
      (η : AdditiveHaarMeasure K.Carrier)
      (μ μinv : Measure (LeftUnipotentQuotient n K.Carrier)),
      QuotientIntegration.IsCompatible (upperUnipotent (n + 1) K.Carrier)
        (generalLinearHaar K.Carrier n) (unipotentHaar K.Carrier n) μ →
      QuotientIntegration.IsCompatible (upperUnipotent (n + 1) K.Carrier)
        (generalLinearHaar K.Carrier n) (unipotentHaar K.Carrier n) μinv →
      ∀ {V : Type uV} [AddCommGroup V] [Module ℂ V]
        {W : Type uW} [AddCommGroup W] [Module ℂ W]
        (π : Representation ℂ (Langlands.GeneralLinear (r + 1) K.Carrier) V)
        (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) K.Carrier) W),
        unequalRankZetaValuesAt j k hr T.residueCardinality ψ (normalizedAbsoluteValue T)
          μ (rectangularMeasure η j (n + 1)) π σ =
        unequalRankZetaValuesAt j k hr T.residueCardinality
          (ψ.scale (-1 : K.Carrierˣ)) (normalizedAbsoluteValue T)
          μinv (rectangularMeasure η j (n + 1)) π σ := by
  subst r
  exact unequalRankZetaValues_scale_neg_one_compatible T n j k

end Compatible

end Langlands.RankinSelberg
