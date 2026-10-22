import Langlands.Representation.RankinSelberg.CharacterChange
import Langlands.Representation.RankinSelberg.LaurentTransport
import Langlands.Representation.RankinSelberg.AnalyticStatement

/-!
# Rational equal-rank zeta transport under change of additive character

The actual integral multiplier is a Laurent unit when the determinant absolute
value is an integer power of q. The quotient measure law remains explicit.
-/

noncomputable section

namespace Langlands.RankinSelberg

open Langlands.GeneralLinear Langlands.Whittaker Langlands.HarmonicAnalysis
open MeasureTheory Polynomial

universe uF uV uV'

variable {F : Type uF} [Field F]

/-- The positive, nonzero quotient modulus, as a complex unit. -/
def characterChangeScalar (abv : AbsoluteValue F ℝ) (a : Fˣ) (n : ℕ) : ℂˣ :=
  Units.mk0 ((characterChangeModulus abv a n : ℝ) : ℂ)
    (Complex.ofReal_ne_zero.mpr (by exact_mod_cast characterChangeModulus_ne_zero abv a n))

/-- The actual Laurent unit multiplying an equal-rank rational zeta value.
Here k is the additive order of det(d_a), so the multiplier is c X^(-k). -/
def characterChangeLaurentUnit (abv : AbsoluteValue F ℝ) (a : Fˣ) (n : ℕ) (k : ℤ) :
    LaurentCoefficientsˣ :=
  laurentMonomialUnit (characterChangeScalar abv a n) (-k)

/-- The determinant weight is an integer spectral power under its numerical
residue-cardinality normalization. Positivity of q fixes the logarithm branch. -/
theorem determinantWeight_eq_spectralPoint_zpow (q : ℕ) (hq : 0 < q)
    (abv : AbsoluteValue F ℝ) {m : ℕ} (g : Langlands.GeneralLinear m F) (k : ℤ)
    (h : abv (Matrix.det g.val) = (q : ℝ) ^ (-k)) (s : ℂ) :
    determinantWeight abv g s = spectralPoint q s ^ k := by
  have harg : Complex.arg (q : ℂ) = 0 := by
    simpa only [Complex.ofReal_natCast] using
      Complex.arg_ofReal_of_nonneg (show 0 ≤ (q : ℝ) by positivity)
  simp only [determinantWeight, h, Complex.ofReal_zpow, Complex.ofReal_natCast]
  rw [← Complex.cpow_int_mul' (by simp [harg, Real.pi_pos])
    (by simpa only [harg, mul_zero] using Real.pi_pos.le)]
  rw [spectralPoint, ← Complex.cpow_int_mul]
  congr 1
  push_cast
  ring

section EqualRank

variable [TopologicalSpace F] [IsTopologicalRing F]
variable (q : ℕ) (hq : 0 < q) (ψ : UnitaryAdditiveCharacter F)
variable (abv : AbsoluteValue F ℝ) (a : Fˣ) {n : ℕ}
variable [MeasurableSpace (LeftUnipotentQuotient n F)]
variable [BorelSpace (LeftUnipotentQuotient n F)]
variable (μ : Measure (LeftUnipotentQuotient n F))
variable (hμ : HasCharacterChangeMeasureLaw abv a μ) (k : ℤ)
variable (hk : abv (Matrix.det (characterChangeElement a n).val) = (q : ℝ) ^ (-k))

include hq hμ hk

/-- Pointwise multiplier of the actual total scalar integrals. -/
theorem equalRankIntegral_characterChange_monomial
    (W : WhittakerFunctions ψ n) (W' : InverseWhittakerFunctions ψ n)
    (Φ : SchwartzBruhat (Fin (n + 1) → F)) (s : ℂ) :
    equalRankIntegral (ψ.scale a) abv μ (characterChangeFunction ψ n a W)
        (characterChangeInverseFunction ψ n a W') Φ s =
      (characterChangeScalar abv a n : ℂ) * spectralPoint q s ^ (-k) *
        equalRankIntegral ψ abv μ W W' Φ s := by
  have hd := determinantWeight_ne_zero abv (characterChangeElement a n) s
  have hD := determinantWeight_eq_spectralPoint_zpow q hq abv
    (characterChangeElement a n) k hk s
  have hi := equalRankIntegral_characterChange ψ abv a μ hμ W W' Φ s
  change _ = (characterChangeScalar abv a n : ℂ) * _ at hi
  calc
    _ = (determinantWeight abv (characterChangeElement a n) s)⁻¹ *
        (determinantWeight abv (characterChangeElement a n) s *
          equalRankIntegral (ψ.scale a) abv μ (characterChangeFunction ψ n a W)
            (characterChangeInverseFunction ψ n a W') Φ s) := by
      rw [← mul_assoc, inv_mul_cancel₀ hd, one_mul]
    _ = _ := by rw [hi, hD, zpow_neg]; ring

/-- The reciprocal multiplier recovers the original integral using the same
measure law and the same translated functions. -/
theorem equalRankIntegral_characterChange_monomial_reverse
    (W : WhittakerFunctions ψ n) (W' : InverseWhittakerFunctions ψ n)
    (Φ : SchwartzBruhat (Fin (n + 1) → F)) (s : ℂ) :
    equalRankIntegral ψ abv μ W W' Φ s =
      (↑(characterChangeScalar abv a n)⁻¹ : ℂ) * spectralPoint q s ^ k *
        equalRankIntegral (ψ.scale a) abv μ (characterChangeFunction ψ n a W)
          (characterChangeInverseFunction ψ n a W') Φ s := by
  have hi := equalRankIntegral_characterChange ψ abv a μ hμ W W' Φ s
  change _ = (characterChangeScalar abv a n : ℂ) * _ at hi
  rw [determinantWeight_eq_spectralPoint_zpow q hq abv
    (characterChangeElement a n) k hk s] at hi
  rw [mul_assoc, hi, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]

/-- Rational continuation is transported by the actual integral multiplier. -/
theorem equalRankContinuation_characterChange
    (W : WhittakerFunctions ψ n) (W' : InverseWhittakerFunctions ψ n)
    (Φ : SchwartzBruhat (Fin (n + 1) → F)) {R : RationalFunctions}
    (hR : HasRationalContinuation q (equalRankIntegral ψ abv μ W W' Φ) R) :
    HasRationalContinuation q
      (equalRankIntegral (ψ.scale a) abv μ (characterChangeFunction ψ n a W)
        (characterChangeInverseFunction ψ n a W') Φ)
      (RatFunc.C (characterChangeScalar abv a n : ℂ) *
        (RatFunc.X : RationalFunctions) ^ (-k) * R) := by
  have h := hR.monomial_mul hq (characterChangeScalar abv a n : ℂ) (-k)
  convert h using 1
  funext s
  exact equalRankIntegral_characterChange_monomial q hq ψ abv a μ hμ k hk W W' Φ s

/-- The reciprocal continuation transport uses the same measure law. -/
theorem equalRankContinuation_characterChange_reverse
    (W : WhittakerFunctions ψ n) (W' : InverseWhittakerFunctions ψ n)
    (Φ : SchwartzBruhat (Fin (n + 1) → F)) {R : RationalFunctions}
    (hR : HasRationalContinuation q
      (equalRankIntegral (ψ.scale a) abv μ (characterChangeFunction ψ n a W)
        (characterChangeInverseFunction ψ n a W') Φ) R) :
    HasRationalContinuation q (equalRankIntegral ψ abv μ W W' Φ)
      (RatFunc.C (↑(characterChangeScalar abv a n)⁻¹ : ℂ) *
        (RatFunc.X : RationalFunctions) ^ k * R) := by
  have h := hR.monomial_mul hq (↑(characterChangeScalar abv a n)⁻¹ : ℂ) k
  convert h using 1
  funext s
  exact equalRankIntegral_characterChange_monomial_reverse q hq ψ abv a μ hμ k hk W W' Φ s

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {V' : Type uV'} [AddCommGroup V'] [Module ℂ V']
variable (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
variable (π' : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V')

/-- Forward transport retains actual coefficient-function and convergence witnesses. -/
theorem equalRankZetaValues_characterChange {R : RationalFunctions}
    (hR : R ∈ equalRankZetaValues q ψ abv μ π π') :
    RatFunc.C (characterChangeScalar abv a n : ℂ) *
      (RatFunc.X : RationalFunctions) ^ (-k) * R ∈
        equalRankZetaValues q (ψ.scale a) abv μ π π' := by
  obtain ⟨W, hW, W', hW', Φ, ⟨b, hb⟩, hr⟩ := hR
  refine ⟨characterChangeFunction ψ n a W, ?_,
    characterChangeInverseFunction ψ n a W', ?_, Φ, ⟨b, ?_⟩, ?_⟩
  · rw [whittakerSet_characterChange ψ a n π]
    exact ⟨W, hW, rfl⟩
  · rw [inverseWhittakerSet_characterChange ψ a n π']
    exact ⟨W', hW', rfl⟩
  · intro s hs
    exact (equalRankConverges_characterChange_iff ψ abv a μ hμ W W' Φ s).2 (hb s hs)
  · exact equalRankContinuation_characterChange q hq ψ abv a μ hμ k hk W W' Φ hr

/-- Reverse transport recovers original coefficient witnesses by surjectivity. -/
theorem equalRankZetaValues_characterChange_reverse {R : RationalFunctions}
    (hR : R ∈ equalRankZetaValues q (ψ.scale a) abv μ π π') :
    RatFunc.C (↑(characterChangeScalar abv a n)⁻¹ : ℂ) *
      (RatFunc.X : RationalFunctions) ^ k * R ∈ equalRankZetaValues q ψ abv μ π π' := by
  obtain ⟨W, hW, W', hW', Φ, ⟨b, hb⟩, hr⟩ := hR
  rw [whittakerSet_characterChange ψ a n π] at hW
  rw [inverseWhittakerSet_characterChange ψ a n π'] at hW'
  obtain ⟨W₀, hW₀, rfl⟩ := hW
  obtain ⟨W₀', hW₀', rfl⟩ := hW'
  refine ⟨W₀, hW₀, W₀', hW₀', Φ, ⟨b, ?_⟩, ?_⟩
  · intro s hs
    exact (equalRankConverges_characterChange_iff ψ abv a μ hμ W₀ W₀' Φ s).1 (hb s hs)
  · exact equalRankContinuation_characterChange_reverse q hq ψ abv a μ hμ k hk W₀ W₀' Φ hr

/-- The intrinsic equal-rank Laurent zeta module is independent of the character
under the stated quotient measure and determinant normalization laws. -/
theorem zetaSpan_equalRank_characterChange :
    zetaSpan (equalRankZetaValues q ψ abv μ π π') =
      zetaSpan (equalRankZetaValues q (ψ.scale a) abv μ π π') := by
  apply zetaSpan_eq_of_monomial_mul (characterChangeScalar abv a n) (-k)
  · exact fun _ h => equalRankZetaValues_characterChange q hq ψ abv a μ hμ k hk π π' h
  · simpa only [neg_neg] using
      (fun R h => equalRankZetaValues_characterChange_reverse q hq ψ abv a μ hμ k hk π π'
        (R := R) h)

/-- The same normalized polynomial generates both equal-rank zeta modules. -/
theorem isEqualRankLPolynomial_characterChange (P : ℂ[X]) :
    IsEqualRankLPolynomial q ψ abv μ π π' P ↔
      IsEqualRankLPolynomial q (ψ.scale a) abv μ π π' P :=
  isNormalizedGenerator_congr
    (zetaSpan_equalRank_characterChange q hq ψ abv a μ hμ k hk π π') P

/-- Existence and uniqueness of a normalized generator transfer with the module. -/
theorem normalizedGeneratorExists_equalRank_characterChange :
    NormalizedGeneratorExists (equalRankZetaValues q ψ abv μ π π') ↔
      NormalizedGeneratorExists (equalRankZetaValues q (ψ.scale a) abv μ π π') :=
  normalizedGeneratorExists_congr
    (zetaSpan_equalRank_characterChange q hq ψ abv a μ hμ k hk π π')

end EqualRank

section Padic

variable {p : ℕ} [Fact p.Prime] {K : PadicField.{uF} p} (T : K.TopologicalData)

/-- The shared p-adic normalization supplies the determinant-order exponent. -/
theorem normalizedDeterminantWeight_eq_spectralPoint_zpow {m : ℕ}
    (g : Langlands.GeneralLinear m K.Carrier) (s : ℂ) :
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
    letI := borel (LeftUnipotentQuotient n K.Carrier)
    letI : BorelSpace (LeftUnipotentQuotient n K.Carrier) := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter K.Carrier) (a : K.Carrierˣ)
      (μ : Measure (LeftUnipotentQuotient n K.Carrier)),
      HasCharacterChangeMeasureLaw (normalizedAbsoluteValue T) a μ →
      ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
        (V' : Type uV') [AddCommGroup V'] [Module ℂ V']
        (π : Representation ℂ (Langlands.GeneralLinear (n + 1) K.Carrier) V)
        (π' : Representation ℂ (Langlands.GeneralLinear (n + 1) K.Carrier) V'),
        zetaSpan (equalRankZetaValues T.residueCardinality ψ
          (normalizedAbsoluteValue T) μ π π') =
        zetaSpan (equalRankZetaValues T.residueCardinality (ψ.scale a)
          (normalizedAbsoluteValue T) μ π π') := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel (LeftUnipotentQuotient n K.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n K.Carrier) := ⟨rfl⟩
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
    letI := borel (LeftUnipotentQuotient n K.Carrier)
    letI : BorelSpace (LeftUnipotentQuotient n K.Carrier) := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter K.Carrier) (a : K.Carrierˣ)
      (μ : Measure (LeftUnipotentQuotient n K.Carrier)),
      HasCharacterChangeMeasureLaw (normalizedAbsoluteValue T) a μ →
      ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
        (V' : Type uV') [AddCommGroup V'] [Module ℂ V']
        (π : Representation ℂ (Langlands.GeneralLinear (n + 1) K.Carrier) V)
        (π' : Representation ℂ (Langlands.GeneralLinear (n + 1) K.Carrier) V') (P : ℂ[X]),
        IsEqualRankLPolynomial T.residueCardinality ψ (normalizedAbsoluteValue T) μ π π' P ↔
        IsEqualRankLPolynomial T.residueCardinality (ψ.scale a)
          (normalizedAbsoluteValue T) μ π π' P := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel (LeftUnipotentQuotient n K.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n K.Carrier) := ⟨rfl⟩
  intro ψ a μ hμ V _ _ V' _ _ π π' P
  exact isNormalizedGenerator_congr
    (zetaSpan_equalRank_characterChange_normalized T n ψ a μ hμ V V' π π') P

end Padic

end Langlands.RankinSelberg
