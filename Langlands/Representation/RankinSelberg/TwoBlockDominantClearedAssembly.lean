import Langlands.Representation.RankinSelberg.TwoBlockDominantLaurentAlgebra

/-!
# Polynomial-cleared two-block coefficient assembly

An internal algebraic reduction. The block equations and the lower Fourier
coefficient law are explicit premises; no analytic identity is asserted here.
-/

noncomputable section

namespace Langlands.RankinSelberg.DominantRankTransport

open HarmonicAnalysis LaurentPolynomial
open HarmonicAnalysis.BilateralLaurentSeries

/-- The finite Laurent reflection is the explicit polynomial substitution
appearing in the first-block Laurent identity. -/
theorem laurentReflection_toLaurent (q : ℂˣ) (P : Polynomial ℂ) :
    laurentReflection q P.toLaurent =
      Polynomial.eval₂ C (C ((q : ℂ)⁻¹) * T (-1)) P := by
  have h :
      (laurentReflection q).toRingHom.comp Polynomial.toLaurent =
        Polynomial.eval₂RingHom C (C ((q : ℂ)⁻¹) * T (-1)) := by
    apply Polynomial.ringHom_ext
    · intro c
      simp
    · simp
  exact congrArg (fun f : Polynomial ℂ →+* LaurentPolynomial ℂ => f P) h

/-- Reflecting the explicit first-block polynomial substitution recovers the
original polynomial, without any statement about bilateral cancellation. -/
theorem laurentReflection_eval₂ (q : ℂˣ) (P : Polynomial ℂ) :
    laurentReflection q
        (Polynomial.eval₂ C (C ((q : ℂ)⁻¹) * T (-1)) P) = P.toLaurent := by
  rw [← laurentReflection_toLaurent, laurentReflection_involutive]

/-- The actual inverse of the reflected nonzero monomial. Only this unit,
rather than an arbitrary polynomial, may be removed from a coefficient law. -/
def inverseReflectedMonomial (q c : ℂˣ) (d : ℤ) : LaurentPolynomial ℂ :=
  C ((c : ℂ)⁻¹ * (q : ℂ) ^ d) * T d

theorem inverseReflectedMonomial_mul (q c : ℂˣ) (d : ℤ) :
    inverseReflectedMonomial q c d *
      laurentReflection q (C (c : ℂ) * T d) = 1 := by
  rw [inverseReflectedMonomial, laurentReflection_C_mul_T]
  calc
    C ((c : ℂ)⁻¹ * (q : ℂ) ^ d) * T d *
        (C ((c : ℂ) * (q : ℂ) ^ (-d)) * T (-d)) =
        C (((c : ℂ)⁻¹ * (q : ℂ) ^ d) * ((c : ℂ) * (q : ℂ) ^ (-d))) *
          (T d * T (-d)) := by simp only [map_mul]; ring
    _ = 1 := by
      have hc : ((c : ℂ)⁻¹ * (q : ℂ) ^ d) *
          ((c : ℂ) * (q : ℂ) ^ (-d)) = 1 := by
        calc
          _ = ((c : ℂ)⁻¹ * (c : ℂ)) *
              ((q : ℂ) ^ d * (q : ℂ) ^ (-d)) := by ring
          _ = 1 := by
            rw [inv_mul_cancel₀ c.ne_zero,
              ← zpow_add₀ q.ne_zero, add_neg_cancel, zpow_zero, one_mul]
      rw [hc, ← T_add, add_neg_cancel, T_zero, map_one, one_mul]

/-- The multiplier obtained from a first-block monomial and the inverse of a
reflected second-block monomial. -/
def clearedProductMultiplier (q c₁ : ℂˣ) (d₁ : ℤ) (c₂ : ℂˣ) (d₂ : ℤ) :
    LaurentPolynomial ℂ :=
  C ((c₁ : ℂ) * (c₂ : ℂ)⁻¹ * (q : ℂ) ^ d₂) * T (d₁ + d₂)

theorem clearedProductMultiplier_eq (q c₁ : ℂˣ) (d₁ : ℤ) (c₂ : ℂˣ) (d₂ : ℤ) :
    clearedProductMultiplier q c₁ d₁ c₂ d₂ =
      inverseReflectedMonomial q c₂ d₂ * (C (c₁ : ℂ) * T d₁) := by
  unfold clearedProductMultiplier inverseReflectedMonomial
  simp only [T_add, map_mul]
  ring

/-- Eliminate the common lower series from two polynomial-cleared block
equations, using the negated-index lower Fourier coefficient law. Both
polynomial denominators remain in the result. -/
theorem twoBlock_cleared_comp (q : ℂˣ)
    {a b aD bD : BilateralLaurentSeries}
    {P₁ P₁D P₂ P₂D : Polynomial ℂ} {M₁ M₂ : LaurentPolynomial ℂ}
    (hFirst : laurentReflection q P₁D.toLaurent • b =
      (M₁ * P₁.toLaurent) • a)
    (hSecond : laurentReflection q P₂.toLaurent • bD =
      (M₂ * P₂D.toLaurent) • aD)
    (hFourier : ∀ k : ℤ, bD (-k) = (q : ℂ) ^ (-k) * b k) :
    (laurentReflection q (P₁D * P₂D).toLaurent *
        laurentReflection q M₂) • bilateralReflection q aD =
      (M₁ * (P₁ * P₂).toLaurent) • a := by
  have hBD : bD = bilateralReflection q b :=
    (eq_bilateralReflection_iff q b bD).2 hFourier
  have hSecondRef := congrArg (bilateralReflection q) hSecond
  rw [bilateralReflection_laurent_smul, bilateralReflection_laurent_smul,
    laurentReflection_involutive, hBD, bilateralReflection_involutive] at hSecondRef
  have h := laurent_cleared_comp hSecondRef hFirst.symm
  have hLeft : P₂.toLaurent * (M₁ * P₁.toLaurent) =
      M₁ * (P₁ * P₂).toLaurent := by rw [map_mul]; ring
  have hRight : laurentReflection q P₁D.toLaurent *
      laurentReflection q (M₂ * P₂D.toLaurent) =
      laurentReflection q (P₁D * P₂D).toLaurent * laurentReflection q M₂ := by
    rw [map_mul, map_mul, map_mul]
    ring
  rw [hLeft, hRight] at h
  exact h.symm

/-- When the block multipliers are nonzero monomials, their unit laws give
the cleared whole-pair identity. Neither polynomial denominator is cancelled.
The common multiplier is explicit, including the power of `q`. -/
theorem twoBlock_monomial_cleared_comp (q c₁ : ℂˣ) (d₁ : ℤ)
    (c₂ : ℂˣ) (d₂ : ℤ)
    {a b aD bD : BilateralLaurentSeries}
    {P₁ P₁D P₂ P₂D : Polynomial ℂ}
    (hFirst : Polynomial.eval₂ C (C ((q : ℂ)⁻¹) * T (-1)) P₁D • b =
      (C (c₁ : ℂ) * T d₁ * P₁.toLaurent) • a)
    (hSecond : Polynomial.eval₂ C (C ((q : ℂ)⁻¹) * T (-1)) P₂ • bD =
      (C (c₂ : ℂ) * T d₂ * P₂D.toLaurent) • aD)
    (hFourier : ∀ k : ℤ, bD (-k) = (q : ℂ) ^ (-k) * b k) :
    Polynomial.eval₂ C (C ((q : ℂ)⁻¹) * T (-1)) (P₁D * P₂D) •
        bilateralReflection q aD =
      (clearedProductMultiplier q c₁ d₁ c₂ d₂ * (P₁ * P₂).toLaurent) • a := by
  rw [← laurentReflection_toLaurent] at hFirst hSecond ⊢
  have h := twoBlock_cleared_comp q hFirst hSecond hFourier
  have hi := congrArg (fun z : BilateralLaurentSeries =>
    inverseReflectedMonomial q c₂ d₂ • z) h
  have hLeft :
      inverseReflectedMonomial q c₂ d₂ *
          (laurentReflection q (P₁D * P₂D).toLaurent *
            laurentReflection q (C (c₂ : ℂ) * T d₂)) =
        laurentReflection q (P₁D * P₂D).toLaurent := by
    calc
      _ = (inverseReflectedMonomial q c₂ d₂ *
          laurentReflection q (C (c₂ : ℂ) * T d₂)) *
            laurentReflection q (P₁D * P₂D).toLaurent := by ring
      _ = _ := by rw [inverseReflectedMonomial_mul, one_mul]
  simp only [← mul_smul] at hi
  rw [hLeft, ← mul_assoc, ← clearedProductMultiplier_eq] at hi
  exact hi

end Langlands.RankinSelberg.DominantRankTransport
