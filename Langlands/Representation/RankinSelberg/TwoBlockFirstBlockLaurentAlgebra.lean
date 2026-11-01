import Langlands.HarmonicAnalysis.BilateralLaurentSeries
import Langlands.Representation.RankinSelberg.EpsilonFactor
import Langlands.Representation.RankinSelberg.EqualRankSwapTransport

/-!
# Finite Laurent algebra for the first-block calculation

Derived algebraic helpers for JPSS (1983), Sections 4.1 and 4.9. The reflected
polynomial is exactly `P(q⁻¹ X⁻¹)`; every action on a bilateral series remains
finite convolution. No polynomial cancellation or analytic comparison is used.
-/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockFirstBlockLaurent

open MeasureTheory LaurentPolynomial HarmonicAnalysis
open HarmonicAnalysis.BilateralLaurentSeries Whittaker

universe uF uV uW

/-- The dual normalized-generator polynomial evaluated at `q⁻¹ X⁻¹`. -/
def reflectedPolynomial (q : ℕ) (P : Polynomial ℂ) : LaurentPolynomial ℂ :=
  P.eval₂ LaurentPolynomial.C
    (LaurentPolynomial.C ((q : ℂ)⁻¹) * LaurentPolynomial.T (-1))

/-- The ordinary polynomial as a finite sum of Laurent monomials. -/
theorem toLaurent_eq_sum (P : Polynomial ℂ) :
    P.toLaurent = ∑ i ∈ P.support,
      LaurentPolynomial.C (P.coeff i) * LaurentPolynomial.T (i : ℤ) := by
  calc
    P.toLaurent = (P.sum fun i c => Polynomial.monomial i c).toLaurent :=
      congrArg Polynomial.toLaurent P.sum_monomial_eq.symm
    _ = _ := by simp only [Polynomial.sum_def, map_sum, Polynomial.toLaurent_C_mul_T]

/-- Reflection changes the exponent from `i` to `-i` and contributes `q⁻ⁱ`. -/
theorem reflectedPolynomial_eq_sum (q : ℕ) (P : Polynomial ℂ) :
    reflectedPolynomial q P = ∑ i ∈ P.support,
      LaurentPolynomial.C (P.coeff i * ((q : ℂ)⁻¹) ^ i) *
        LaurentPolynomial.T (-(i : ℤ)) := by
  simp only [reflectedPolynomial, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_pow, ← map_pow, LaurentPolynomial.T_pow, ← mul_assoc, ← map_mul]
  simp

/-- Ordinary polynomial action, expressed using its natural-number support. -/
theorem toLaurent_smul_apply (P : Polynomial ℂ) (Z : BilateralLaurentSeries) (k : ℤ) :
    (P.toLaurent • Z) k = ∑ i ∈ P.support, P.coeff i * Z (k - (i : ℤ)) := by
  rw [toLaurent_eq_sum, Finset.sum_smul, sum_apply]
  simp only [C_mul_T_smul_apply]

/-- Reflected polynomial action uses the coefficients at `k+i`. -/
theorem reflectedPolynomial_smul_apply (q : ℕ) (P : Polynomial ℂ)
    (Z : BilateralLaurentSeries) (k : ℤ) :
    (reflectedPolynomial q P • Z) k = ∑ i ∈ P.support,
      (P.coeff i * ((q : ℂ)⁻¹) ^ i) * Z (k + (i : ℤ)) := by
  rw [reflectedPolynomial_eq_sum, Finset.sum_smul, sum_apply]
  simp only [C_mul_T_smul_apply, sub_neg_eq_add]

/-- The epsilon monomial and ordinary polynomial give the prescribed shifted sum. -/
theorem epsilonPolynomial_smul_apply (c : ℂ) (d : ℤ) (P : Polynomial ℂ)
    (Z : BilateralLaurentSeries) (k : ℤ) :
    ((LaurentPolynomial.C c * LaurentPolynomial.T d * P.toLaurent) • Z) k =
      c * ∑ i ∈ P.support, P.coeff i * Z (k - d - (i : ℤ)) := by
  rw [mul_smul, C_mul_T_smul_apply, toLaurent_smul_apply]

/-- The prescribed Laurent identity is precisely the equality of its finite coefficient sums. -/
theorem identity_iff_coefficients (q : ℕ) (P Pdual : Polynomial ℂ) (c : ℂ) (d : ℤ)
    (Zup Zlow : BilateralLaurentSeries) :
    reflectedPolynomial q Pdual • Zlow =
      (LaurentPolynomial.C c * LaurentPolynomial.T d * P.toLaurent) • Zup ↔
    ∀ k : ℤ, (∑ i ∈ Pdual.support,
      (Pdual.coeff i * ((q : ℂ)⁻¹) ^ i) * Zlow (k + (i : ℤ))) =
      c * ∑ i ∈ P.support, P.coeff i * Zup (k - d - (i : ℤ)) := by
  constructor
  · intro h k
    simpa only [reflectedPolynomial_smul_apply, epsilonPolynomial_smul_apply] using
      congrArg (fun Z : BilateralLaurentSeries => Z k) h
  · intro h
    ext k
    simpa only [reflectedPolynomial_smul_apply, epsilonPolynomial_smul_apply] using h k

section Integration

variable {A : Type*} [MeasurableSpace A] {μ : Measure A}
  {S U : A → BilateralLaurentSeries}

/-- Integration of the finite reflected coefficient sum. -/
theorem reflectedPolynomial_integral_apply (q : ℕ) (P : Polynomial ℂ)
    (hS : CoeffwiseIntegrable S μ) (k : ℤ) :
    ∫ x, (∑ i ∈ P.support,
      (P.coeff i * ((q : ℂ)⁻¹) ^ i) * S x (k + (i : ℤ))) ∂μ =
      (reflectedPolynomial q P • coeffwiseIntegral μ S) k := by
  simp only [← reflectedPolynomial_smul_apply]
  exact congrArg (fun Z : BilateralLaurentSeries => Z k)
    (coeffwiseIntegral_laurent_smul (reflectedPolynomial q P) hS)

/-- Integrate a pointwise finite Laurent identity with the same polynomial witnesses. -/
theorem integral_laurent_identity (D Q : LaurentPolynomial ℂ)
    (hS : CoeffwiseIntegrable S μ) (hU : CoeffwiseIntegrable U μ)
    (h : ∀ x, D • S x = Q • U x) :
    D • coeffwiseIntegral μ S = Q • coeffwiseIntegral μ U := by
  rw [← coeffwiseIntegral_laurent_smul D hS,
    ← coeffwiseIntegral_laurent_smul Q hU]
  congr 1
  funext x
  exact h x

end Integration

/-- The reciprocal cube-mass comparison cancels the upper unfolding scalar. -/
theorem cube_mass_cancel {c : ℝ} (hc : c ≠ 0)
    {Zup Zmixed Zradical : BilateralLaurentSeries}
    (hup : Zup = c • Zmixed) (hlow : Zradical = c • Zmixed) :
    Zup = Zradical ∧ c⁻¹ • Zup = Zmixed := by
  constructor
  · exact hup.trans hlow.symm
  · rw [hup, smul_smul, inv_mul_cancel₀ hc, one_smul]

/-- A sign scalar of square one has every natural-number power of square one. -/
theorem scalar_pow_mul_self (ζ : ℂˣ) (hζ : ζ ^ 2 = 1) (t : ℕ) :
    (ζ : ℂ) ^ t * (ζ : ℂ) ^ t = 1 := by
  calc
    (ζ : ℂ) ^ t * (ζ : ℂ) ^ t = ((ζ : ℂ) ^ 2) ^ t := by ring
    _ = 1 := by
      have h : (ζ : ℂ) ^ 2 = 1 := congrArg (fun z : ℂˣ => (z : ℂ)) hζ
      rw [h, one_pow]

/-- Reverse the JPSS scalar orientation using only the involutive sign scalar. -/
theorem orient_laurent_identity (ζ : ℂˣ) (hζ : ζ ^ 2 = 1) (t : ℕ)
    (c : ℂ) (d : ℤ) (P : Polynomial ℂ) (D : LaurentPolynomial ℂ)
    (Zup Zlow : BilateralLaurentSeries)
    (h : (LaurentPolynomial.C c * LaurentPolynomial.T d * P.toLaurent) • Zup =
      (LaurentPolynomial.C ((ζ : ℂ) ^ t) * D) • Zlow) :
    D • Zlow = (LaurentPolynomial.C ((ζ : ℂ) ^ t * c) *
      LaurentPolynomial.T d * P.toLaurent) • Zup := by
  have hh := congrArg (fun Z : BilateralLaurentSeries => (ζ : ℂ) ^ t • Z) h
  simp only [mul_smul, C_smul] at hh ⊢
  simp only [smul_smul, scalar_pow_mul_self ζ hζ t, one_smul] at hh ⊢
  exact hh.symm

section ModelScalar

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [MeasurableSpace F] {n r : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ}
  {μ : Measure (LeftUnipotentQuotient n F)}
  {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}
  {ℓ : glFunctionals ψ r π} {ℓ' : glInverseFunctionals ψ n σ}

omit [IsTopologicalRing F] [MeasurableSpace F] in
/-- An actual normalized generator forces both supplied functionals to be nonzero.
This consequence is used only within the conditional epsilon clause. -/
theorem normalizedGenerator_functionals_ne_zero (hq : 1 < q)
    (j k : ℕ) (hr : r = n + (j + k + 1))
    [MeasurableSpace (Matrix (Fin j) (Fin (n + 1)) F)]
    {ρ : Measure (Matrix (Fin j) (Fin (n + 1)) F)} {P : Polynomial ℂ}
    (hP : IsNormalizedGenerator (unequalRankValuesAt j k hr q ψ abv μ ρ π σ ℓ ℓ') P) :
    ℓ.val ≠ 0 ∧ ℓ'.val ≠ 0 := by
  subst r
  obtain ⟨R, hRmem, hR0⟩ := hP.exists_ne_zero
  obtain ⟨f, f', hR⟩ := hRmem
  have hnonzero : f.val ≠ 0 ∧ f'.val ≠ 0 := by
    constructor
    · intro hf
      change HasRationalContinuation q (unequalRankIntegral ψ abv j k μ ρ f.val f'.val) R at hR
      rw [unequalRankIntegral_eq_zero j k μ ρ (Or.inl hf)] at hR
      exact hR0 (eq_zero_of_hasRationalContinuation_zero hq hR)
    · intro hf'
      change HasRationalContinuation q (unequalRankIntegral ψ abv j k μ ρ f.val f'.val) R at hR
      rw [unequalRankIntegral_eq_zero j k μ ρ (Or.inr hf')] at hR
      exact hR0 (eq_zero_of_hasRationalContinuation_zero hq hR)
  constructor
  · intro hℓ
    apply hnonzero.1
    obtain ⟨v, rfl⟩ := modelMap_surjective π ℓ f
    ext g
    change ℓ.val (π g v) = 0
    rw [hℓ]
    rfl
  · intro hℓ'
    apply hnonzero.2
    obtain ⟨v, rfl⟩ := modelMap_surjective σ ℓ' f'
    ext g
    change ℓ'.val (σ g v) = 0
    rw [hℓ']
    rfl

omit [IsTopologicalRing F] [MeasurableSpace F] in
/-- The actual minus-one scalar is involutive whenever a normalized generator is supplied. -/
theorem minusOneScalar_sq_eq_one (hq : 1 < q)
    (j k : ℕ) (hr : r = n + (j + k + 1))
    [MeasurableSpace (Matrix (Fin j) (Fin (n + 1)) F)]
    {ρ : Measure (Matrix (Fin j) (Fin (n + 1)) F)} {P : Polynomial ℂ}
    (hP : IsNormalizedGenerator (unequalRankValuesAt j k hr q ψ abv μ ρ π σ ℓ ℓ') P)
    {ζ : ℂˣ} (hζ : HasModelMinusOneScalar σ ℓ' ζ) : ζ ^ 2 = 1 :=
  hζ.sq_eq_one (normalizedGenerator_functionals_ne_zero hq j k hr hP).2

end ModelScalar

end Langlands.RankinSelberg.TwoBlockFirstBlockLaurent
