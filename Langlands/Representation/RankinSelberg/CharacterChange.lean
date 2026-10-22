import Langlands.Representation.Whittaker.CharacterChange
import Langlands.Representation.RankinSelberg.LocalFactor

/-!
# Quotient transport for a change of additive character

Left translation by the character-change diagonal acts on the left-unipotent
quotient. Its measure scaling is an explicit obligation, separate from the
algebraic translation of Whittaker functions and from zeta-value transport.
-/

noncomputable section

namespace Langlands.RankinSelberg

open Langlands.GeneralLinear Langlands.Whittaker Langlands.HarmonicAnalysis
open MeasureTheory
open scoped NNReal ENNReal

universe uF uV

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]

omit [TopologicalSpace F] [IsTopologicalRing F] in
/-- Conjugation by the character-change diagonal preserves membership in N. -/
theorem characterChange_mem_unipotent_iff (a : Fˣ) (n : ℕ)
    (g : Langlands.GeneralLinear (n + 1) F) :
    characterChangeElement a n * g * (characterChangeElement a n)⁻¹ ∈
      upperUnipotent (n + 1) F ↔ g ∈ upperUnipotent (n + 1) F := by
  constructor
  · intro h
    have h' := (characterChangeConj a⁻¹ n ⟨_, h⟩).property
    change characterChangeElement a⁻¹ n *
      (characterChangeElement a n * g * (characterChangeElement a n)⁻¹) *
      (characterChangeElement a⁻¹ n)⁻¹ ∈ upperUnipotent (n + 1) F at h'
    simpa only [← characterChangeElement_inv, inv_inv, inv_mul_cancel_left,
      mul_assoc, inv_mul_cancel_right, inv_mul_cancel, mul_one] using h'
  · intro h
    exact (characterChangeConj a n ⟨g, h⟩).property

/-- The map `N g ↦ N d_a g` on the actual left quotient. -/
def characterChangeQuotient (a : Fˣ) (n : ℕ) :
    LeftUnipotentQuotient n F ≃ₜ LeftUnipotentQuotient n F :=
  Homeomorph.Quotient.congr (Homeomorph.mulLeft (characterChangeElement a n)) (by
    intro x y
    rw [QuotientGroup.rightRel_apply, QuotientGroup.rightRel_apply]
    change y * x⁻¹ ∈ upperUnipotent (n + 1) F ↔
      (characterChangeElement a n * y) * (characterChangeElement a n * x)⁻¹ ∈ _
    rw [mul_inv_rev]
    simpa only [mul_assoc] using (characterChange_mem_unipotent_iff a n (y * x⁻¹)).symm)

@[simp] theorem characterChangeQuotient_mk (a : Fˣ) (n : ℕ)
    (g : Langlands.GeneralLinear (n + 1) F) :
    characterChangeQuotient a n (Quotient.mk _ g) =
      Quotient.mk _ (characterChangeElement a n * g) := rfl

/-- Scaling back gives the inverse quotient translation. -/
theorem characterChangeQuotient_inv (a : Fˣ) (n : ℕ) :
    (characterChangeQuotient a n).symm = characterChangeQuotient a⁻¹ n := by
  ext q
  induction q using Quotient.inductionOn with
  | h g =>
    change Quotient.mk _ ((characterChangeElement a n)⁻¹ * g) =
      Quotient.mk _ (characterChangeElement a⁻¹ n * g)
    rw [characterChangeElement_inv]

/-- Sum of the positive-root exponents for `diag(a^n,...,1)`. -/
def characterChangeRootExponent (n : ℕ) : ℕ :=
  ∑ i : Fin (n + 1), ∑ j : Fin (n + 1), if i < j then j.val - i.val else 0

/-- The expected unipotent conjugation modulus `|a|^(sum_{i<j}(j-i))`. -/
def characterChangeModulus (abv : AbsoluteValue F ℝ) (a : Fˣ) (n : ℕ) : ℝ≥0 :=
  ⟨abv (a : F) ^ characterChangeRootExponent n, pow_nonneg (abv.nonneg _) _⟩

omit [TopologicalSpace F] [IsTopologicalRing F] in
theorem characterChangeModulus_ne_zero (abv : AbsoluteValue F ℝ) (a : Fˣ) (n : ℕ) :
    characterChangeModulus abv a n ≠ 0 := by
  intro h
  exact pow_ne_zero (characterChangeRootExponent n) (abv.ne_zero (Units.ne_zero a))
    (congrArg (fun x : ℝ≥0 => (x : ℝ)) h)

section Measure

variable {n : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)]
variable [BorelSpace (LeftUnipotentQuotient n F)]

/-- The precise missing measure law: the pushforward of quotient Haar measure
under left multiplication by `d_a` is its unipotent conjugation modulus times
that measure. This is a property, not an existence assertion. -/
def HasCharacterChangeMeasureLaw (abv : AbsoluteValue F ℝ) (a : Fˣ)
    (μ : Measure (LeftUnipotentQuotient n F)) : Prop :=
  Measure.map (characterChangeQuotient a n) μ =
    (characterChangeModulus abv a n : ℝ≥0∞) • μ

/-- Change of variables for arbitrary complex functions, conditional on the
explicit pushforward law; total Bochner integrals need no integrability input. -/
theorem integral_characterChangeQuotient (abv : AbsoluteValue F ℝ) (a : Fˣ)
    (μ : Measure (LeftUnipotentQuotient n F)) (hμ : HasCharacterChangeMeasureLaw abv a μ)
    (f : LeftUnipotentQuotient n F → ℂ) :
    (∫ q, f (characterChangeQuotient a n q) ∂μ) =
      (characterChangeModulus abv a n : ℝ) • ∫ q, f q ∂μ := by
  change (∫ q, f ((characterChangeQuotient a n).toMeasurableEquiv q) ∂μ) = _
  rw [← integral_map_equiv (characterChangeQuotient a n).toMeasurableEquiv f]
  change (∫ q, f q ∂Measure.map (characterChangeQuotient a n) μ) = _
  rw [hμ, integral_smul_measure]
  simp

/-- The measure law preserves integrability because its scalar is finite and nonzero. -/
theorem integrable_characterChangeQuotient_iff (abv : AbsoluteValue F ℝ) (a : Fˣ)
    (μ : Measure (LeftUnipotentQuotient n F)) (hμ : HasCharacterChangeMeasureLaw abv a μ)
    (f : LeftUnipotentQuotient n F → ℂ) :
    Integrable (fun q => f (characterChangeQuotient a n q)) μ ↔ Integrable f μ := by
  change Integrable (f ∘ (characterChangeQuotient a n).toMeasurableEquiv) μ ↔ _
  rw [← integrable_map_equiv (characterChangeQuotient a n).toMeasurableEquiv f]
  change Integrable f (Measure.map (characterChangeQuotient a n) μ) ↔ _
  rw [hμ]
  exact integrable_smul_measure
    (by exact_mod_cast characterChangeModulus_ne_zero abv a n) ENNReal.coe_ne_top

end Measure

section WhittakerSets

variable (ψ : UnitaryAdditiveCharacter F) (a : Fˣ) (n : ℕ)
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)

/-- Intrinsic Whittaker sets are carried exactly onto one another by left translation. -/
theorem whittakerSet_characterChange :
    whittakerSet (ψ.scale a) n π =
      characterChangeFunction ψ n a '' whittakerSet ψ n π := by
  ext W
  constructor
  · rintro ⟨ℓ, v, rfl⟩
    obtain ⟨ℓ₀, rfl⟩ := (characterChangeFunctionalEquiv ψ π a).surjective ℓ
    refine ⟨coefficientMap π ℓ₀ v, ⟨ℓ₀, v, rfl⟩, ?_⟩
    ext g
    exact (characterChangeFunctional_coefficient ψ π a ℓ₀ v g).symm
  · rintro ⟨W, ⟨ℓ, v, rfl⟩, rfl⟩
    refine ⟨characterChangeFunctional ψ π a ℓ, v, ?_⟩
    ext g
    exact characterChangeFunctional_coefficient ψ π a ℓ v g

/-- The same transport for the inverse-character member of a pair. -/
theorem inverseWhittakerSet_characterChange :
    inverseWhittakerSet (ψ.scale a) n π =
      characterChangeInverseFunction ψ n a '' inverseWhittakerSet ψ n π := by
  ext W
  constructor
  · rintro ⟨ℓ, v, rfl⟩
    obtain ⟨ℓ₀, rfl⟩ := (characterChangeInverseFunctionalEquiv ψ π a).surjective ℓ
    refine ⟨coefficientMap π ℓ₀ v, ⟨ℓ₀, v, rfl⟩, ?_⟩
    ext g
    exact (characterChangeInverseFunctional_coefficient ψ π a ℓ₀ v g).symm
  · rintro ⟨W, ⟨ℓ, v, rfl⟩, rfl⟩
    refine ⟨characterChangeInverseFunctional ψ π a ℓ, v, ?_⟩
    ext g
    exact characterChangeInverseFunctional_coefficient ψ π a ℓ v g

end WhittakerSets

section EqualRank

omit [TopologicalSpace F] [IsTopologicalRing F] in
/-- The character-change diagonal fixes the last row under left multiplication. -/
theorem lastRow_characterChangeElement_mul (a : Fˣ) (n : ℕ)
    (g : Langlands.GeneralLinear (n + 1) F) :
    lastRow (characterChangeElement a n * g) = lastRow g := by
  funext j
  simp [lastRow, Units.val_mul, characterChangeElement_val, Matrix.diagonal_mul]

omit [TopologicalSpace F] [IsTopologicalRing F] in
/-- Multiplicativity of the positive-real determinant weight. -/
theorem determinantWeight_mul (abv : AbsoluteValue F ℝ) {m : ℕ}
    (g h : Langlands.GeneralLinear m F) (s : ℂ) :
    determinantWeight abv (g * h) s =
      determinantWeight abv g s * determinantWeight abv h s := by
  simp only [determinantWeight, Units.val_mul, Matrix.det_mul, map_mul,
    Complex.ofReal_mul]
  exact Complex.mul_cpow_ofReal_nonneg (abv.nonneg _) (abv.nonneg _) s

omit [TopologicalSpace F] [IsTopologicalRing F] in
/-- The determinant weight of an invertible matrix is nonzero for every complex s. -/
theorem determinantWeight_ne_zero (abv : AbsoluteValue F ℝ) {m : ℕ}
    (g : Langlands.GeneralLinear m F) (s : ℂ) : determinantWeight abv g s ≠ 0 := by
  exact Complex.cpow_ne_zero_iff.mpr
    (Or.inl (Complex.ofReal_ne_zero.mpr (abv.ne_zero g.det_ne_zero)))

variable (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ) (a : Fˣ) {n : ℕ}

/-- The exact equal-rank integrand identity on the quotient. The test function is
unchanged because the last diagonal entry of d_a is one. -/
theorem equalRankIntegrand_characterChange
    (W : WhittakerFunctions ψ n) (W' : InverseWhittakerFunctions ψ n)
    (Φ : SchwartzBruhat (Fin (n + 1) → F)) (s : ℂ) (q : LeftUnipotentQuotient n F) :
    equalRankIntegrand ψ abv W W' Φ s (characterChangeQuotient a n q) =
      determinantWeight abv (characterChangeElement a n) s *
        equalRankIntegrand (ψ.scale a) abv (characterChangeFunction ψ n a W)
          (characterChangeInverseFunction ψ n a W') Φ s q := by
  induction q using Quotient.inductionOn with
  | h g =>
    simp only [characterChangeQuotient_mk, equalRankIntegrand_mk,
      lastRow_characterChangeElement_mul, determinantWeight_mul,
      characterChangeFunction_apply, characterChangeInverseFunction_apply]
    ring

variable [MeasurableSpace (LeftUnipotentQuotient n F)]
variable [BorelSpace (LeftUnipotentQuotient n F)]
variable (μ : Measure (LeftUnipotentQuotient n F))

/-- The conditional change-of-character formula for actual scalar integrals. -/
theorem equalRankIntegral_characterChange (hμ : HasCharacterChangeMeasureLaw abv a μ)
    (W : WhittakerFunctions ψ n) (W' : InverseWhittakerFunctions ψ n)
    (Φ : SchwartzBruhat (Fin (n + 1) → F)) (s : ℂ) :
    determinantWeight abv (characterChangeElement a n) s *
      equalRankIntegral (ψ.scale a) abv μ (characterChangeFunction ψ n a W)
        (characterChangeInverseFunction ψ n a W') Φ s =
    (characterChangeModulus abv a n : ℝ) • equalRankIntegral ψ abv μ W W' Φ s := by
  unfold equalRankIntegral
  rw [← integral_const_mul]
  simp_rw [← equalRankIntegrand_characterChange]
  exact integral_characterChangeQuotient abv a μ hμ _

/-- Absolute convergence is unchanged for the translated equal-rank data,
under the same explicit measure law. -/
theorem equalRankConverges_characterChange_iff (hμ : HasCharacterChangeMeasureLaw abv a μ)
    (W : WhittakerFunctions ψ n) (W' : InverseWhittakerFunctions ψ n)
    (Φ : SchwartzBruhat (Fin (n + 1) → F)) (s : ℂ) :
    EqualRankConverges (ψ.scale a) abv μ (characterChangeFunction ψ n a W)
      (characterChangeInverseFunction ψ n a W') Φ s ↔
      EqualRankConverges ψ abv μ W W' Φ s := by
  have h := integrable_characterChangeQuotient_iff abv a μ hμ
    (equalRankIntegrand ψ abv W W' Φ s)
  simp_rw [equalRankIntegrand_characterChange] at h
  rw [integrable_const_mul_iff (isUnit_iff_ne_zero.mpr
    (determinantWeight_ne_zero abv (characterChangeElement a n) s))] at h
  exact h

end EqualRank

end Langlands.RankinSelberg
