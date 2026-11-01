import Langlands.Representation.RankinSelberg.TwoBlockDominantClearedAssembly
import Langlands.HarmonicAnalysis.BilateralLaurentClearingProof

/-!
# Finite numerators in the dominant-rank coefficient assembly

An internal application of the published bilateral Laurent clearing theorem.
The coefficient equations and one-sided support bounds are explicit premises.
-/

noncomputable section

namespace Langlands.RankinSelberg.DominantRankTransport

open HarmonicAnalysis LaurentPolynomial
open HarmonicAnalysis.BilateralLaurentSeries

/-- Reflection changes a lower support bound into an upper support bound. -/
theorem bilateralReflection_upperSupport (q : ℂˣ)
    {a : BilateralLaurentSeries} (ha : HasLowerBoundedSupport a) :
    HasUpperBoundedSupport (bilateralReflection q a) := by
  obtain ⟨N, hN⟩ := (hasLowerBoundedSupport_iff a).1 ha
  refine (hasUpperBoundedSupport_iff _).2 ⟨-N, fun n hn => ?_⟩
  rw [bilateralReflection_apply, hN (-n) (by omega), mul_zero]

/-- Reflection changes an upper support bound into a lower support bound. -/
theorem bilateralReflection_lowerSupport (q : ℂˣ)
    {a : BilateralLaurentSeries} (ha : HasUpperBoundedSupport a) :
    HasLowerBoundedSupport (bilateralReflection q a) := by
  obtain ⟨N, hN⟩ := (hasUpperBoundedSupport_iff a).1 ha
  refine (hasLowerBoundedSupport_iff _).2 ⟨-N, fun n hn => ?_⟩
  rw [bilateralReflection_apply, hN (-n) (by omega), mul_zero]

theorem bilateralReflection_upperSupport_iff (q : ℂˣ) (a : BilateralLaurentSeries) :
    HasUpperBoundedSupport (bilateralReflection q a) ↔ HasLowerBoundedSupport a := by
  constructor
  · intro ha
    simpa only [bilateralReflection_involutive] using bilateralReflection_lowerSupport q ha
  · exact bilateralReflection_upperSupport q

theorem bilateralReflection_lowerSupport_iff (q : ℂˣ) (a : BilateralLaurentSeries) :
    HasLowerBoundedSupport (bilateralReflection q a) ↔ HasUpperBoundedSupport a := by
  constructor
  · intro ha
    simpa only [bilateralReflection_involutive] using bilateralReflection_upperSupport q ha
  · exact bilateralReflection_lowerSupport q

/-- The finite and bilateral reflection maps agree on Laurent coefficients. -/
theorem bilateralReflection_ofLaurentPolynomial (q : ℂˣ) (R : LaurentPolynomial ℂ) :
    bilateralReflection q (ofLaurentPolynomial R) =
      ofLaurentPolynomial (laurentReflection q R) := by
  have hOne : bilateralReflection q (ofLaurentPolynomial 1) =
      ofLaurentPolynomial 1 := by
    ext n
    change (q : ℂ) ^ n * (1 : LaurentPolynomial ℂ).coeff (-n) =
      (1 : LaurentPolynomial ℂ).coeff n
    change (q : ℂ) ^ n * (T 0 : LaurentPolynomial ℂ).coeff (-n) =
      (T 0 : LaurentPolynomial ℂ).coeff n
    by_cases hn : n = 0
    · subst n
      simp
    · have h0n : (0 : ℤ) ≠ n := Ne.symm hn
      have h0neg : (0 : ℤ) ≠ -n := by omega
      simp only [T_apply, ite_eq_right h0n, ite_eq_right h0neg, mul_zero]
  calc
    bilateralReflection q (ofLaurentPolynomial R) =
        bilateralReflection q (R • ofLaurentPolynomial 1) := by
          rw [← ofLaurentPolynomial_mul, mul_one]
    _ = laurentReflection q R • ofLaurentPolynomial 1 := by
      rw [bilateralReflection_laurent_smul, hOne]
    _ = ofLaurentPolynomial (laurentReflection q R) := by
      rw [← ofLaurentPolynomial_mul, mul_one]

/-- Opposite one-sided bounds extract a unique finite numerator and its
reflected dual numerator. Both clearing factors are retained. -/
theorem existsUnique_reflectedClearedNumerator (q : ℂˣ)
    {a aD : BilateralLaurentSeries} {A B : LaurentPolynomial ℂ}
    (ha : HasLowerBoundedSupport a) (haD : HasLowerBoundedSupport aD)
    (h : A • a = laurentReflection q B • bilateralReflection q aD) :
    ∃! R : LaurentPolynomial ℂ,
      ofLaurentPolynomial R = A • a ∧
      ofLaurentPolynomial (laurentReflection q R) = B • aD := by
  obtain ⟨R, hR, _⟩ := bilateralLaurentClearing a (bilateralReflection q aD)
    A (laurentReflection q B) ha (bilateralReflection_upperSupport q haD) h
  have hDual := congrArg (bilateralReflection q) hR.2
  rw [bilateralReflection_ofLaurentPolynomial, bilateralReflection_laurent_smul,
    laurentReflection_involutive, bilateralReflection_involutive] at hDual
  exact ⟨R, ⟨hR.1, hDual⟩,
    fun S hS => ofLaurentPolynomial_injective (hS.1.trans hR.1.symm)⟩

/-- The unique Laurent numerator of a supplied reflected clearing equation.
No support or coefficient equation for an actual JPSS section is asserted. -/
def reflectedClearedNumerator (q : ℂˣ)
    (a aD : BilateralLaurentSeries) (A B : LaurentPolynomial ℂ)
    (ha : HasLowerBoundedSupport a) (haD : HasLowerBoundedSupport aD)
    (h : A • a = laurentReflection q B • bilateralReflection q aD) :
    LaurentPolynomial ℂ :=
  Classical.choose (existsUnique_reflectedClearedNumerator q ha haD h)

theorem reflectedClearedNumerator_spec (q : ℂˣ)
    (a aD : BilateralLaurentSeries) (A B : LaurentPolynomial ℂ)
    (ha : HasLowerBoundedSupport a) (haD : HasLowerBoundedSupport aD)
    (h : A • a = laurentReflection q B • bilateralReflection q aD) :
    ofLaurentPolynomial (reflectedClearedNumerator q a aD A B ha haD h) = A • a ∧
      ofLaurentPolynomial
        (laurentReflection q (reflectedClearedNumerator q a aD A B ha haD h)) =
          B • aD :=
  (Classical.choose_spec (existsUnique_reflectedClearedNumerator q ha haD h)).1

/-- The whole-pair multiplier is a unit, since each of its factors is a
nonzero constant or a Laurent monomial. -/
def clearedProductMultiplierUnit (q c₁ : ℂˣ) (d₁ : ℤ) (c₂ : ℂˣ) (d₂ : ℤ) :
    (LaurentPolynomial ℂ)ˣ :=
  Units.map C.toMonoidHom (c₁ * c₂⁻¹ * q ^ d₂) *
    (isUnit_T (d₁ + d₂)).unit

@[simp]
theorem coe_clearedProductMultiplierUnit
    (q c₁ : ℂˣ) (d₁ : ℤ) (c₂ : ℂˣ) (d₂ : ℤ) :
    (clearedProductMultiplierUnit q c₁ d₁ c₂ d₂ : LaurentPolynomial ℂ) =
      clearedProductMultiplier q c₁ d₁ c₂ d₂ := by
  simp only [clearedProductMultiplierUnit, Units.val_mul, Units.coe_map,
    IsUnit.unit_spec, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val]
  rfl

/-- A proved Laurent unit may be removed from the supplied reflected equation.
The numerator on the original side is cleared by `A` itself. -/
theorem existsUnique_reflectedClearedNumerator_of_unit (q : ℂˣ)
    (M : (LaurentPolynomial ℂ)ˣ)
    {a aD : BilateralLaurentSeries} {A B : LaurentPolynomial ℂ}
    (ha : HasLowerBoundedSupport a) (haD : HasLowerBoundedSupport aD)
    (h : laurentReflection q B • bilateralReflection q aD = ((M : LaurentPolynomial ℂ) * A) • a) :
    ∃! R : LaurentPolynomial ℂ,
      ofLaurentPolynomial R = A • a ∧
      ofLaurentPolynomial (laurentReflection q R) =
        (laurentReflection q (↑M⁻¹ : LaurentPolynomial ℂ) * B) • aD := by
  have h' := congrArg (fun z : BilateralLaurentSeries =>
    (↑M⁻¹ : LaurentPolynomial ℂ) • z) h
  simp only [← mul_smul, ← mul_assoc, Units.inv_mul, one_mul] at h'
  apply existsUnique_reflectedClearedNumerator q ha haD
  simpa only [map_mul, laurentReflection_involutive] using h'.symm

/-- Two supplied block equations, the lower Fourier coefficient law and the
support bounds produce a finite numerator cleared by the product of the two
original polynomials. The dual product remains multiplied by a Laurent unit. -/
theorem twoBlock_cleared_numerators (q c₁ : ℂˣ) (d₁ : ℤ) (c₂ : ℂˣ) (d₂ : ℤ)
    {a b aD bD : BilateralLaurentSeries}
    {P₁ P₁D P₂ P₂D : Polynomial ℂ}
    (ha : HasLowerBoundedSupport a) (haD : HasLowerBoundedSupport aD)
    (hFirst : Polynomial.eval₂ C (C ((q : ℂ)⁻¹) * T (-1)) P₁D • b =
      (C (c₁ : ℂ) * T d₁ * P₁.toLaurent) • a)
    (hSecond : Polynomial.eval₂ C (C ((q : ℂ)⁻¹) * T (-1)) P₂ • bD =
      (C (c₂ : ℂ) * T d₂ * P₂D.toLaurent) • aD)
    (hFourier : ∀ k : ℤ, bD (-k) = (q : ℂ) ^ (-k) * b k) :
    ∃! R : LaurentPolynomial ℂ,
      ofLaurentPolynomial R = (P₁ * P₂).toLaurent • a ∧
      ofLaurentPolynomial (laurentReflection q R) =
        (laurentReflection q
          (↑(clearedProductMultiplierUnit q c₁ d₁ c₂ d₂)⁻¹ : LaurentPolynomial ℂ) *
            (P₁D * P₂D).toLaurent) • aD := by
  apply existsUnique_reflectedClearedNumerator_of_unit q
    (clearedProductMultiplierUnit q c₁ d₁ c₂ d₂) ha haD
  rw [coe_clearedProductMultiplierUnit, laurentReflection_toLaurent]
  exact twoBlock_monomial_cleared_comp q c₁ d₁ c₂ d₂ hFirst hSecond hFourier

end Langlands.RankinSelberg.DominantRankTransport
