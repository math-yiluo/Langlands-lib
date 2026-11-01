import Langlands.HarmonicAnalysis.BilateralLaurentSeries

/-!
# Laurent reflection in the dominant-rank assembly

Elementary coefficient algebra for the substitution `X ↦ q⁻¹ X⁻¹`.
The bilateral series have no support restriction, and the composition
lemmas do not cancel Laurent polynomials acting on them.
-/

noncomputable section

namespace Langlands.RankinSelberg.DominantRankTransport

open HarmonicAnalysis LaurentPolynomial
open HarmonicAnalysis.BilateralLaurentSeries

/-- Reflection of bilateral coefficients corresponding to `X ↦ q⁻¹ X⁻¹`. -/
def bilateralReflection (q : ℂˣ) :
    BilateralLaurentSeries ≃ₗ[ℂ] BilateralLaurentSeries where
  toFun a n := (q : ℂ) ^ n * a (-n)
  invFun a n := (q : ℂ) ^ n * a (-n)
  left_inv a := by
    ext n
    simp only [neg_neg, ← mul_assoc, ← zpow_add₀ (Units.ne_zero q),
      add_neg_cancel, zpow_zero, one_mul]
  right_inv a := by
    ext n
    simp only [neg_neg, ← mul_assoc, ← zpow_add₀ (Units.ne_zero q),
      add_neg_cancel, zpow_zero, one_mul]
  map_add' a b := by
    ext n
    exact mul_add _ _ _
  map_smul' c a := by
    ext n
    change (q : ℂ) ^ n * (c * a (-n)) = c * ((q : ℂ) ^ n * a (-n))
    ring

@[simp]
theorem bilateralReflection_apply (q : ℂˣ) (a : BilateralLaurentSeries) (n : ℤ) :
    bilateralReflection q a n = (q : ℂ) ^ n * a (-n) := rfl

@[simp]
theorem bilateralReflection_involutive (q : ℂˣ) (a : BilateralLaurentSeries) :
    bilateralReflection q (bilateralReflection q a) = a :=
  (bilateralReflection q).left_inv a

/-- The coefficient law with negated index is exactly reflected equality. -/
theorem eq_bilateralReflection_iff (q : ℂˣ) (a b : BilateralLaurentSeries) :
    b = bilateralReflection q a ↔
      ∀ k : ℤ, b (-k) = (q : ℂ) ^ (-k) * a k := by
  constructor
  · rintro rfl k
    simp
  · intro h
    ext n
    simpa only [neg_neg, bilateralReflection_apply] using h (-n)

/-- The image of a Laurent monomial under the reflected substitution. -/
def laurentReflectionMonomial (q : ℂˣ) :
    Multiplicative ℤ →* LaurentPolynomial ℂ where
  toFun m := C ((q : ℂ) ^ (-m.toAdd)) * T (-m.toAdd)
  map_one' := by simp
  map_mul' j k := by
    change C ((q : ℂ) ^ (-(j.toAdd + k.toAdd))) * T (-(j.toAdd + k.toAdd)) =
      (C ((q : ℂ) ^ (-j.toAdd)) * T (-j.toAdd)) *
        (C ((q : ℂ) ^ (-k.toAdd)) * T (-k.toAdd))
    simp only [neg_add, zpow_add₀ (Units.ne_zero q),
      map_mul, T_add]
    ring

/-- Finite Laurent-polynomial substitution `X ↦ q⁻¹ X⁻¹`. -/
def laurentReflection (q : ℂˣ) :
    LaurentPolynomial ℂ →ₐ[ℂ] LaurentPolynomial ℂ :=
  AddMonoidAlgebra.lift ℂ (LaurentPolynomial ℂ) ℤ (laurentReflectionMonomial q)

@[simp]
theorem laurentReflection_C_mul_T (q : ℂˣ) (c : ℂ) (m : ℤ) :
    laurentReflection q (C c * T m) = C (c * (q : ℂ) ^ (-m)) * T (-m) := by
  rw [← single_eq_C_mul_T, laurentReflection, AddMonoidAlgebra.lift_single]
  change c • (C ((q : ℂ) ^ (-m)) * T (-m)) = _
  rw [LaurentPolynomial.smul_eq_C_mul, ← mul_assoc, ← map_mul]

@[simp]
theorem laurentReflection_C (q : ℂˣ) (c : ℂ) :
    laurentReflection q (C c) = C c := by
  simpa using laurentReflection_C_mul_T q c 0

@[simp]
theorem laurentReflection_T (q : ℂˣ) (m : ℤ) :
    laurentReflection q (T m) = C ((q : ℂ) ^ (-m)) * T (-m) := by
  simpa using laurentReflection_C_mul_T q 1 m

@[simp]
theorem laurentReflection_involutive (q : ℂˣ) (P : LaurentPolynomial ℂ) :
    laurentReflection q (laurentReflection q P) = P := by
  induction P using LaurentPolynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | C_mul_T m c =>
      rw [laurentReflection_C_mul_T, laurentReflection_C_mul_T]
      simp only [neg_neg]
      have hz : (q : ℂ) ^ (-m) * (q : ℂ) ^ m = 1 := by
        rw [← zpow_add₀ (Units.ne_zero q), neg_add_cancel, zpow_zero]
      rw [mul_assoc, hz, mul_one]

/-- Reflection transports the finite Laurent action on arbitrary bilateral
series. It requires neither convergence nor a support bound. -/
theorem bilateralReflection_laurent_smul (q : ℂˣ)
    (P : LaurentPolynomial ℂ) (a : BilateralLaurentSeries) :
    bilateralReflection q (P • a) =
      laurentReflection q P • bilateralReflection q a := by
  induction P using LaurentPolynomial.induction_on' with
  | add P Q hP hQ =>
      simp only [add_smul, map_add, hP, hQ]
  | C_mul_T m c =>
      ext n
      simp only [bilateralReflection_apply, C_mul_T_smul_apply,
        laurentReflection_C_mul_T]
      have hi : -(n - -m) = -n - m := by omega
      have hz : (q : ℂ) ^ (-m) * (q : ℂ) ^ (n - -m) = (q : ℂ) ^ n := by
        rw [← zpow_add₀ (Units.ne_zero q)]
        congr 1
        omega
      rw [hi]
      calc
        (q : ℂ) ^ n * (c * a (-n - m)) =
            c * ((q : ℂ) ^ n * a (-n - m)) := by ring
        _ = c * (((q : ℂ) ^ (-m) * (q : ℂ) ^ (n - -m)) *
            a (-n - m)) := by rw [hz]
        _ = (c * (q : ℂ) ^ (-m)) *
            ((q : ℂ) ^ (n - -m) * a (-n - m)) := by ring

/-- Reflection preserves coefficientwise integrability for every supplied
measure, by applying a fixed scalar to each reflected coefficient. -/
theorem coeffwiseIntegrable_bilateralReflection (q : ℂˣ)
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    {s : Ω → BilateralLaurentSeries} (hs : CoeffwiseIntegrable s μ) :
    CoeffwiseIntegrable (fun x => bilateralReflection q (s x)) μ :=
  fun n => (hs (-n)).const_mul ((q : ℂ) ^ n)

/-- Coefficientwise integration commutes with reflection. -/
theorem coeffwiseIntegral_bilateralReflection (q : ℂˣ)
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (s : Ω → BilateralLaurentSeries) :
    coeffwiseIntegral μ (fun x => bilateralReflection q (s x)) =
      bilateralReflection q (coeffwiseIntegral μ s) := by
  ext n
  exact MeasureTheory.integral_const_mul _ _

/-- Two polynomial-cleared equations compose by multiplication. Bilateral
series may have Laurent torsion, so no cancellation is used. -/
theorem laurent_cleared_comp
    {a b c : BilateralLaurentSeries} {A B C D : LaurentPolynomial ℂ}
    (hAB : A • b = B • a) (hCD : C • c = D • b) :
    (A * C) • c = (D * B) • a := by
  rw [mul_smul, hCD, ← mul_smul, mul_comm A D, mul_smul, hAB, ← mul_smul]

/-- Composition after reflecting the first polynomial-cleared equation.
Both denominators remain in the resulting identity. -/
theorem laurent_cleared_reflection_comp (q : ℂˣ)
    {a b c : BilateralLaurentSeries} {A B C D : LaurentPolynomial ℂ}
    (hAB : A • b = B • a) (hCD : C • c = D • bilateralReflection q b) :
    (laurentReflection q A * C) • c =
      (D * laurentReflection q B) • bilateralReflection q a := by
  have hRef := congrArg (bilateralReflection q) hAB
  simp only [bilateralReflection_laurent_smul] at hRef
  exact laurent_cleared_comp hRef hCD

end Langlands.RankinSelberg.DominantRankTransport
