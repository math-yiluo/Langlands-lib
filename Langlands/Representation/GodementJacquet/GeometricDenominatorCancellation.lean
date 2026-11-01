import Langlands.Representation.RankinSelberg.LaurentTransport
import Langlands.Representation.RankinSelberg.RationalEvaluation

/-! # Cancellation of reciprocal geometric Laurent denominators -/

noncomputable section

namespace Langlands.GodementJacquet

open RankinSelberg LocalFactor

/-- Reciprocal substitution within the actual Laurent coefficient ring. -/
def laurentReciprocal (δ : ℂˣ) : LaurentCoefficients →+* LaurentCoefficients :=
  LaurentPolynomial.eval₂ LaurentPolynomial.C (laurentMonomialUnit δ (-1))

@[simp] theorem laurentReciprocal_C (δ : ℂˣ) (c : ℂ) :
    laurentReciprocal δ (LaurentPolynomial.C c) = LaurentPolynomial.C c := by
  exact LaurentPolynomial.eval₂_C _ _ _

private theorem laurentToRatFunc_unit_zpow (u : LaurentCoefficientsˣ) (k : ℤ) :
    laurentToRatFunc ((u ^ k : LaurentCoefficientsˣ) : LaurentCoefficients) =
      (laurentToRatFunc (u : LaurentCoefficients)) ^ k := by
  change ((Units.map laurentToRatFunc.toMonoidHom (u ^ k) : RationalFunctionsˣ) :
    RationalFunctions) = _
  rw [map_zpow, Units.val_zpow_eq_zpow_val, Units.coe_map]
  rfl

private theorem subst_C (δ : ℂˣ) (c : ℂ) :
    RationalReflection.subst δ (RatFunc.C c) = RatFunc.C c := by
  change RationalReflection.subst δ (algebraMap ℂ RationalFunctions c) =
    algebraMap ℂ RationalFunctions c
  exact (RationalReflection.subst δ).commutes c

/-- Reciprocal substitution commutes with the genuine Laurent embedding. -/
theorem laurentToRatFunc_reciprocal (δ : ℂˣ) (A : LaurentCoefficients) :
    laurentToRatFunc (laurentReciprocal δ A) =
      RationalReflection.subst δ (laurentToRatFunc A) := by
  induction A using LaurentPolynomial.induction_on' with
  | add A B hA hB => simp only [map_add, hA, hB]
  | C_mul_T k c =>
    simp only [map_mul, laurentReciprocal, LaurentPolynomial.eval₂_C,
      laurentToRatFunc_C, LaurentPolynomial.eval₂_T, laurentToRatFunc_unit_zpow,
      laurentToRatFunc_monomialUnit, laurentToRatFunc_T, map_zpow₀,
      RationalReflection.subst_X, subst_C,
      RationalReflection.reflectedVariable, div_eq_mul_inv, zpow_neg_one]
    rfl

/-- The reflected geometric denominator has the reciprocal exponent and the
expected scalar coefficient. -/
theorem subst_geometricDenominator (δ : ℂˣ) (β : ℂ) (k : ℤ) :
    RationalReflection.subst δ
        (laurentToRatFunc (1 - LaurentPolynomial.C β * LaurentPolynomial.T k)) =
      laurentToRatFunc
        (1 - LaurentPolynomial.C (β * (δ : ℂ) ^ k) * LaurentPolynomial.T (-k)) := by
  simp only [map_sub, map_one, map_mul, laurentToRatFunc_C, laurentToRatFunc_T,
    map_zpow₀, RationalReflection.subst_X, subst_C,
    RationalReflection.reflectedVariable, div_eq_mul_inv, zpow_neg, mul_zpow, inv_zpow]
  change 1 - RatFunc.C β * (RatFunc.C (δ : ℂ) ^ k * (RatFunc.X ^ k)⁻¹) =
    1 - RatFunc.C β * RatFunc.C (δ : ℂ) ^ k * (RatFunc.X ^ k)⁻¹
  ring

/-- Two reciprocal geometric denominators admit an explicit constant Bézout
combination whenever the product of their coefficients differs from one. -/
theorem exists_laurent_of_geometric_clearings
    (α β : ℂ) (k : ℤ) (hαβ : α * β ≠ 1) {R : RationalFunctions}
    (hD : ∃ A : LaurentCoefficients, laurentToRatFunc A =
      laurentToRatFunc (1 - LaurentPolynomial.C α * LaurentPolynomial.T k) * R)
    (hE : ∃ B : LaurentCoefficients, laurentToRatFunc B =
      laurentToRatFunc (1 - LaurentPolynomial.C β * LaurentPolynomial.T (-k)) * R) :
    ∃ A : LaurentCoefficients, laurentToRatFunc A = R := by
  obtain ⟨A, hA⟩ := hD
  obtain ⟨B, hB⟩ := hE
  let M : LaurentCoefficients := LaurentPolynomial.C β * LaurentPolynomial.T (-k)
  have hMD : M * (LaurentPolynomial.C α * LaurentPolynomial.T k) =
      LaurentPolynomial.C (α * β) := by
    dsimp only [M]
    rw [mul_mul_mul_comm, ← map_mul, ← LaurentPolynomial.T_add]
    simp only [neg_add_cancel, LaurentPolynomial.T_zero, mul_one, mul_comm β α]
  have hbez :
      (1 - M) + M * (1 - LaurentPolynomial.C α * LaurentPolynomial.T k) =
        LaurentPolynomial.C (1 - α * β) := by
    rw [mul_sub, mul_one, hMD, map_sub, map_one]
    ring
  have hc : (1 - α * β : ℂ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hαβ)
  refine ⟨LaurentPolynomial.C (1 - α * β)⁻¹ * (B + M * A), ?_⟩
  rw [map_mul, map_add, map_mul, hA, hB]
  change laurentToRatFunc (LaurentPolynomial.C (1 - α * β)⁻¹) *
    (laurentToRatFunc (1 - M) * R +
      laurentToRatFunc M *
        (laurentToRatFunc (1 - LaurentPolynomial.C α * LaurentPolynomial.T k) * R)) = R
  rw [← mul_assoc (laurentToRatFunc M), ← add_mul, ← map_mul, ← map_add, hbez,
    ← mul_assoc, ← map_mul, ← map_mul, inv_mul_cancel₀ hc, map_one, map_one, one_mul]

/-- A Laurent monomial functional equation transports dual denominator
clearing to the reciprocal denominator on the original rational value. -/
theorem exists_laurent_of_reflected_geometric_clearings
    (δ : ℂˣ) (α β : ℂ) (k : ℤ) (hαβ : α * (β * (δ : ℂ) ^ k) ≠ 1)
    (u : LaurentCoefficientsˣ) {R RDual : RationalFunctions}
    (hD : ∃ A : LaurentCoefficients, laurentToRatFunc A =
      laurentToRatFunc (1 - LaurentPolynomial.C α * LaurentPolynomial.T k) * R)
    (hE : ∃ B : LaurentCoefficients, laurentToRatFunc B =
      laurentToRatFunc (1 - LaurentPolynomial.C β * LaurentPolynomial.T k) * RDual)
    (hFE : RationalReflection.subst δ RDual =
      laurentToRatFunc (u : LaurentCoefficients) * R) :
    ∃ A : LaurentCoefficients, laurentToRatFunc A = R := by
  apply exists_laurent_of_geometric_clearings α (β * (δ : ℂ) ^ k) k hαβ hD
  obtain ⟨B, hB⟩ := hE
  refine ⟨(u⁻¹ : LaurentCoefficientsˣ) * laurentReciprocal δ B, ?_⟩
  rw [map_mul, laurentToRatFunc_reciprocal, hB, map_mul,
    subst_geometricDenominator, hFE]
  calc
    _ = laurentToRatFunc
        (1 - LaurentPolynomial.C (β * (δ : ℂ) ^ k) * LaurentPolynomial.T (-k)) *
        ((laurentToRatFunc (u⁻¹ : LaurentCoefficientsˣ) *
          laurentToRatFunc (u : LaurentCoefficients)) * R) := by ring
    _ = _ := by rw [← map_mul, Units.inv_mul, map_one, one_mul]

end Langlands.GodementJacquet
