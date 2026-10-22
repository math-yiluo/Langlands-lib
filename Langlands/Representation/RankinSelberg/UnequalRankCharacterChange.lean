import Langlands.Representation.RankinSelberg.UnequalRankCharacterIntegrals
import Langlands.Representation.RankinSelberg.EqualRankCharacterChange

/-!
# Conditional rational unequal-rank transport under change of character
-/

noncomputable section

namespace Langlands.RankinSelberg

open Langlands.GeneralLinear Langlands.Whittaker Langlands.HarmonicAnalysis
open MeasureTheory Polynomial

universe uF uV uV'

variable {F : Type uF} [Field F]

/-- The nonzero constant in the unequal-rank integral multiplier. The denominator
retains the half-gap shift in the actual determinant weight. -/
def unequalRankCharacterChangeScalar (abv : AbsoluteValue F ℝ) (a : Fˣ) (n j k : ℕ) :
    ℂˣ :=
  characterChangeScalar abv a n *
    Units.mk0 ((characterChangeRectangularModulus abv a j n : ℝ) : ℂ)
      (Complex.ofReal_ne_zero.mpr (by
        exact_mod_cast characterChangeRectangularModulus_ne_zero abv a j n)) /
    Units.mk0 (determinantWeight abv (characterChangeElement a n)
      (-((j + k + 1 : ℕ) : ℂ) / 2)) (determinantWeight_ne_zero _ _ _)

@[simp] theorem unequalRankCharacterChangeScalar_val
    (abv : AbsoluteValue F ℝ) (a : Fˣ) (n j k : ℕ) :
    (unequalRankCharacterChangeScalar abv a n j k : ℂ) =
      ((characterChangeModulus abv a n : ℝ) : ℂ) *
        ((characterChangeRectangularModulus abv a j n : ℝ) : ℂ) /
          determinantWeight abv (characterChangeElement a n)
            (-((j + k + 1 : ℕ) : ℂ) / 2) := rfl

/-- The Laurent unit multiplying an unequal-rank rational zeta value. -/
def unequalRankCharacterChangeLaurentUnit (abv : AbsoluteValue F ℝ) (a : Fˣ)
    (n j k : ℕ) (e : ℤ) : LaurentCoefficientsˣ :=
  laurentMonomialUnit (unequalRankCharacterChangeScalar abv a n j k) (-e)

/-- The spectral shift factors through an actual nonzero constant. -/
theorem determinantWeight_shift_eq_spectralPoint_zpow (q : ℕ) (hq : 0 < q)
    (abv : AbsoluteValue F ℝ) {m : ℕ} (g : Langlands.GeneralLinear m F) (e : ℤ)
    (h : abv (Matrix.det g.val) = (q : ℝ) ^ (-e)) (s t : ℂ) :
    determinantWeight abv g (s + t) =
      spectralPoint q s ^ e * determinantWeight abv g t := by
  have hd : ((abv (Matrix.det g.val) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (abv.ne_zero g.det_ne_zero)
  rw [show determinantWeight abv g (s + t) =
      determinantWeight abv g s * determinantWeight abv g t from Complex.cpow_add s t hd,
    determinantWeight_eq_spectralPoint_zpow q hq abv g e h s]

section UnequalRank

variable [TopologicalSpace F] [IsTopologicalRing F]
variable (q : ℕ) (hq : 0 < q) (ψ : UnitaryAdditiveCharacter F)
variable (abv : AbsoluteValue F ℝ) (a : Fˣ) {n : ℕ} (j k : ℕ)
variable [MeasurableSpace (LeftUnipotentQuotient n F)]
variable [BorelSpace (LeftUnipotentQuotient n F)]
variable [MeasurableSpace (Matrix (Fin j) (Fin (n + 1)) F)]
variable [BorelSpace (Matrix (Fin j) (Fin (n + 1)) F)]
variable (μ : Measure (LeftUnipotentQuotient n F))
variable (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F))
variable (hμ : HasCharacterChangeMeasureLaw abv a μ)
variable (hν : HasCharacterChangeRectangularMeasureLaw abv a j n ν)
variable (e : ℤ)
variable (he : abv (Matrix.det (characterChangeElement a n).val) = (q : ℝ) ^ (-e))

include hq hμ hν he

/-- Pointwise Laurent-monomial multiplier of the actual iterated integrals. -/
theorem unequalRankIntegral_characterChange_monomial
    (W : WhittakerFunctions ψ (n + (j + k + 1)))
    (W' : InverseWhittakerFunctions ψ n) (s : ℂ) :
    unequalRankIntegral (ψ.scale a) abv j k μ ν
        (unequalRankCharacterChangeFunction ψ a n j k W)
        (characterChangeInverseFunction ψ n a W') s =
      (unequalRankCharacterChangeScalar abv a n j k : ℂ) * spectralPoint q s ^ (-e) *
        unequalRankIntegral ψ abv j k μ ν W W' s := by
  have hx : spectralPoint q s ^ e ≠ 0 := zpow_ne_zero _
    (Complex.cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hq))))
  have hA := determinantWeight_ne_zero abv (characterChangeElement a n)
    (-((j + k + 1 : ℕ) : ℂ) / 2)
  have hD := determinantWeight_shift_eq_spectralPoint_zpow q hq abv
    (characterChangeElement a n) e he s (-((j + k + 1 : ℕ) : ℂ) / 2)
  rw [neg_div, ← sub_eq_add_neg] at hD
  have hi := unequalRankIntegral_characterChange abv a j n μ ν ψ k hμ hν W W' s
  rw [hD] at hi
  rw [neg_div] at hA
  apply (mul_left_cancel₀ (mul_ne_zero hx hA))
  calc
    _ = _ := by simpa only [neg_div] using hi
    _ = _ := by
      rw [unequalRankCharacterChangeScalar_val, zpow_neg]
      field_simp [hA, hx]

/-- The reciprocal multiplier recovers the original total integral. -/
theorem unequalRankIntegral_characterChange_monomial_reverse
    (W : WhittakerFunctions ψ (n + (j + k + 1)))
    (W' : InverseWhittakerFunctions ψ n) (s : ℂ) :
    unequalRankIntegral ψ abv j k μ ν W W' s =
      (↑(unequalRankCharacterChangeScalar abv a n j k)⁻¹ : ℂ) * spectralPoint q s ^ e *
        unequalRankIntegral (ψ.scale a) abv j k μ ν
          (unequalRankCharacterChangeFunction ψ a n j k W)
          (characterChangeInverseFunction ψ n a W') s := by
  rw [unequalRankIntegral_characterChange_monomial q hq ψ abv a j k μ ν hμ hν e he]
  have hx : spectralPoint q s ^ e ≠ 0 := zpow_ne_zero _
    (Complex.cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hq))))
  rw [zpow_neg]
  have hc := Units.ne_zero (unequalRankCharacterChangeScalar abv a n j k)
  simp only [Units.val_inv_eq_inv_val]
  field_simp

/-- Rational continuation transports by the actual integral multiplier. -/
theorem unequalRankContinuation_characterChange
    (W : WhittakerFunctions ψ (n + (j + k + 1)))
    (W' : InverseWhittakerFunctions ψ n) {R : RationalFunctions}
    (hR : HasRationalContinuation q (unequalRankIntegral ψ abv j k μ ν W W') R) :
    HasRationalContinuation q
      (unequalRankIntegral (ψ.scale a) abv j k μ ν
        (unequalRankCharacterChangeFunction ψ a n j k W)
        (characterChangeInverseFunction ψ n a W'))
      (RatFunc.C (unequalRankCharacterChangeScalar abv a n j k : ℂ) *
        (RatFunc.X : RationalFunctions) ^ (-e) * R) := by
  have h := hR.monomial_mul hq (unequalRankCharacterChangeScalar abv a n j k : ℂ) (-e)
  convert h using 1
  funext s
  exact unequalRankIntegral_characterChange_monomial q hq ψ abv a j k μ ν hμ hν e he W W' s

/-- Reciprocal continuation transport uses the same measure laws. -/
theorem unequalRankContinuation_characterChange_reverse
    (W : WhittakerFunctions ψ (n + (j + k + 1)))
    (W' : InverseWhittakerFunctions ψ n) {R : RationalFunctions}
    (hR : HasRationalContinuation q
      (unequalRankIntegral (ψ.scale a) abv j k μ ν
        (unequalRankCharacterChangeFunction ψ a n j k W)
        (characterChangeInverseFunction ψ n a W')) R) :
    HasRationalContinuation q (unequalRankIntegral ψ abv j k μ ν W W')
      (RatFunc.C (↑(unequalRankCharacterChangeScalar abv a n j k)⁻¹ : ℂ) *
        (RatFunc.X : RationalFunctions) ^ e * R) := by
  have h := hR.monomial_mul hq (↑(unequalRankCharacterChangeScalar abv a n j k)⁻¹ : ℂ) e
  convert h using 1
  funext s
  exact unequalRankIntegral_characterChange_monomial_reverse q hq ψ abv a j k μ ν hμ hν e he W W' s

variable [SFinite μ] [SFinite ν]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {V' : Type uV'} [AddCommGroup V'] [Module ℂ V']
variable (π : Representation ℂ (Langlands.GeneralLinear (n + (j + k + 1) + 1) F) V)
variable (π' : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V')

/-- Forward transport retains the actual coefficient and convergence witnesses. -/
theorem unequalRankZetaValues_characterChange {R : RationalFunctions}
    (hR : R ∈ unequalRankZetaValues q ψ abv j k μ ν π π') :
    RatFunc.C (unequalRankCharacterChangeScalar abv a n j k : ℂ) *
      (RatFunc.X : RationalFunctions) ^ (-e) * R ∈
        unequalRankZetaValues q (ψ.scale a) abv j k μ ν π π' := by
  obtain ⟨W, hW, W', hW', ⟨b, hb⟩, hr⟩ := hR
  refine ⟨unequalRankCharacterChangeFunction ψ a n j k W, ?_,
    characterChangeInverseFunction ψ n a W', ?_, ⟨b, ?_⟩, ?_⟩
  · rw [whittakerSet_unequalRankCharacterChange ψ a n j k π]
    exact ⟨W, hW, rfl⟩
  · rw [inverseWhittakerSet_characterChange ψ a n π']
    exact ⟨W', hW', rfl⟩
  · intro s hs
    exact (unequalRankConverges_characterChange_iff abv a j n μ ν ψ k hμ hν W W' s).2 (hb s hs)
  · exact unequalRankContinuation_characterChange q hq ψ abv a j k μ ν hμ hν e he W W' hr

/-- Reverse transport recovers the original functional and vector witnesses. -/
theorem unequalRankZetaValues_characterChange_reverse {R : RationalFunctions}
    (hR : R ∈ unequalRankZetaValues q (ψ.scale a) abv j k μ ν π π') :
    RatFunc.C (↑(unequalRankCharacterChangeScalar abv a n j k)⁻¹ : ℂ) *
      (RatFunc.X : RationalFunctions) ^ e * R ∈
        unequalRankZetaValues q ψ abv j k μ ν π π' := by
  obtain ⟨W, hW, W', hW', ⟨b, hb⟩, hr⟩ := hR
  rw [whittakerSet_unequalRankCharacterChange ψ a n j k π] at hW
  rw [inverseWhittakerSet_characterChange ψ a n π'] at hW'
  obtain ⟨W₀, hW₀, rfl⟩ := hW
  obtain ⟨W₀', hW₀', rfl⟩ := hW'
  refine ⟨W₀, hW₀, W₀', hW₀', ⟨b, ?_⟩, ?_⟩
  · intro s hs
    exact (unequalRankConverges_characterChange_iff abv a j n μ ν ψ k hμ hν W₀ W₀' s).1 (hb s hs)
  · exact unequalRankContinuation_characterChange_reverse q hq ψ abv a j k μ ν hμ hν e he
      W₀ W₀' hr

/-- Conditional character independence of the intrinsic unequal-rank Laurent span. -/
theorem zetaSpan_unequalRank_characterChange :
    zetaSpan (unequalRankZetaValues q ψ abv j k μ ν π π') =
      zetaSpan (unequalRankZetaValues q (ψ.scale a) abv j k μ ν π π') := by
  apply zetaSpan_eq_of_monomial_mul (unequalRankCharacterChangeScalar abv a n j k) (-e)
  · exact fun _ h => unequalRankZetaValues_characterChange q hq ψ abv a j k μ ν hμ hν e he π π' h
  · simpa only [neg_neg] using
      (fun R h => unequalRankZetaValues_characterChange_reverse q hq ψ abv a j k μ ν hμ hν e he
        π π' (R := R) h)

/-- The same normalized polynomial generates both unequal-rank zeta modules. -/
theorem isUnequalRankLPolynomial_characterChange (P : ℂ[X]) :
    IsUnequalRankLPolynomial q ψ abv j k μ ν π π' P ↔
      IsUnequalRankLPolynomial q (ψ.scale a) abv j k μ ν π π' P :=
  isNormalizedGenerator_congr
    (zetaSpan_unequalRank_characterChange q hq ψ abv a j k μ ν hμ hν e he π π') P

/-- Existence and uniqueness of a normalized generator transfer with the module. -/
theorem normalizedGeneratorExists_unequalRank_characterChange :
    NormalizedGeneratorExists (unequalRankZetaValues q ψ abv j k μ ν π π') ↔
      NormalizedGeneratorExists (unequalRankZetaValues q (ψ.scale a) abv j k μ ν π π') :=
  normalizedGeneratorExists_congr
    (zetaSpan_unequalRank_characterChange q hq ψ abv a j k μ ν hμ hν e he π π')

end UnequalRank

section Padic

variable {p : ℕ} [Fact p.Prime] {K : PadicField.{uF} p} (T : K.TopologicalData)

/-- P-adic unequal-rank span invariance with the numerical determinant
normalization discharged by the actual valuation. Both measure laws remain explicit. -/
theorem zetaSpan_unequalRank_characterChange_normalized (n j k : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel (LeftUnipotentQuotient n K.Carrier)
    letI : BorelSpace (LeftUnipotentQuotient n K.Carrier) := ⟨rfl⟩
    letI := borel (Matrix (Fin j) (Fin (n + 1)) K.Carrier)
    letI : BorelSpace (Matrix (Fin j) (Fin (n + 1)) K.Carrier) := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter K.Carrier) (a : K.Carrierˣ)
      (μ : Measure (LeftUnipotentQuotient n K.Carrier))
      (ν : Measure (Matrix (Fin j) (Fin (n + 1)) K.Carrier)) [SFinite μ] [SFinite ν],
      HasCharacterChangeMeasureLaw (normalizedAbsoluteValue T) a μ →
      HasCharacterChangeRectangularMeasureLaw (normalizedAbsoluteValue T) a j n ν →
      ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
        (V' : Type uV') [AddCommGroup V'] [Module ℂ V']
        (π : Representation ℂ (Langlands.GeneralLinear (n + (j + k + 1) + 1) K.Carrier) V)
        (π' : Representation ℂ (Langlands.GeneralLinear (n + 1) K.Carrier) V'),
        zetaSpan (unequalRankZetaValues T.residueCardinality ψ
          (normalizedAbsoluteValue T) j k μ ν π π') =
        zetaSpan (unequalRankZetaValues T.residueCardinality (ψ.scale a)
          (normalizedAbsoluteValue T) j k μ ν π π') := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel (LeftUnipotentQuotient n K.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n K.Carrier) := ⟨rfl⟩
  let := borel (Matrix (Fin j) (Fin (n + 1)) K.Carrier)
  let : BorelSpace (Matrix (Fin j) (Fin (n + 1)) K.Carrier) := ⟨rfl⟩
  intro ψ a μ ν _ _ hμ hν V _ _ V' _ _ π π'
  exact zetaSpan_unequalRank_characterChange T.residueCardinality
    (Nat.zero_lt_one.trans T.residueCardinality_gt_one) ψ (normalizedAbsoluteValue T)
    a j k μ ν hμ hν (T.ord (Matrix.det (characterChangeElement a n).val))
    (T.normalizedAbs_of_ne_zero (characterChangeElement a n).det_ne_zero) π π'

/-- Under the same measure laws, p-adic normalized L-polynomial relations agree.
This does not assert existence of either normalized generator. -/
theorem isUnequalRankLPolynomial_characterChange_normalized (n j k : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel (LeftUnipotentQuotient n K.Carrier)
    letI : BorelSpace (LeftUnipotentQuotient n K.Carrier) := ⟨rfl⟩
    letI := borel (Matrix (Fin j) (Fin (n + 1)) K.Carrier)
    letI : BorelSpace (Matrix (Fin j) (Fin (n + 1)) K.Carrier) := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter K.Carrier) (a : K.Carrierˣ)
      (μ : Measure (LeftUnipotentQuotient n K.Carrier))
      (ν : Measure (Matrix (Fin j) (Fin (n + 1)) K.Carrier)) [SFinite μ] [SFinite ν],
      HasCharacterChangeMeasureLaw (normalizedAbsoluteValue T) a μ →
      HasCharacterChangeRectangularMeasureLaw (normalizedAbsoluteValue T) a j n ν →
      ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
        (V' : Type uV') [AddCommGroup V'] [Module ℂ V']
        (π : Representation ℂ (Langlands.GeneralLinear (n + (j + k + 1) + 1) K.Carrier) V)
        (π' : Representation ℂ (Langlands.GeneralLinear (n + 1) K.Carrier) V') (P : ℂ[X]),
        IsUnequalRankLPolynomial T.residueCardinality ψ
          (normalizedAbsoluteValue T) j k μ ν π π' P ↔
        IsUnequalRankLPolynomial T.residueCardinality (ψ.scale a)
          (normalizedAbsoluteValue T) j k μ ν π π' P := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel (LeftUnipotentQuotient n K.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n K.Carrier) := ⟨rfl⟩
  let := borel (Matrix (Fin j) (Fin (n + 1)) K.Carrier)
  let : BorelSpace (Matrix (Fin j) (Fin (n + 1)) K.Carrier) := ⟨rfl⟩
  intro ψ a μ ν _ _ hμ hν V _ _ V' _ _ π π' P
  exact isNormalizedGenerator_congr
    (zetaSpan_unequalRank_characterChange_normalized T n j k ψ a μ ν hμ hν V V' π π') P

end Padic

end Langlands.RankinSelberg
