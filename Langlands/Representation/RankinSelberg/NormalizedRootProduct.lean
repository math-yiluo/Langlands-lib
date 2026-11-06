import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.Separable

/-! # Normalized products over reciprocal polynomial roots -/

noncomputable section

namespace Langlands.RankinSelberg

open Polynomial

/-- The finite set of reciprocals of the complex roots of a polynomial. -/
def reciprocalRootParameters (P : ℂ[X]) : Finset ℂ := by
  classical
  exact P.roots.toFinset.image Inv.inv

theorem mem_reciprocalRootParameters {P : ℂ[X]} (hP : P.coeff 0 = 1) (a : ℂ) :
    a ∈ reciprocalRootParameters P ↔ a ≠ 0 ∧ P.eval a⁻¹ = 0 := by
  classical
  have hPne : P ≠ 0 := by
    intro hz
    simp [hz] at hP
  constructor
  · rintro ha
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
    have hxroot : P.eval x = 0 := (mem_roots hPne).mp (Multiset.mem_toFinset.mp hx)
    have hxne : x ≠ 0 := by
      intro hz
      rw [hz, ← coeff_zero_eq_eval_zero, hP] at hxroot
      exact one_ne_zero hxroot
    exact ⟨inv_ne_zero hxne, by simpa using hxroot⟩
  · rintro ⟨ha, hroot⟩
    exact Finset.mem_image.mpr ⟨a⁻¹,
      Multiset.mem_toFinset.mpr ((mem_roots hPne).mpr hroot), inv_inv a⟩

/-- A separable complex polynomial with constant coefficient one is exactly
the product of its normalized linear factors, once for each reciprocal root. -/
theorem eq_prod_reciprocalRootParameters {P : ℂ[X]}
    (hP : P.coeff 0 = 1) (hsep : P.Separable) :
    P = ∏ a ∈ reciprocalRootParameters P, (1 - C a * X) := by
  classical
  let S := P.roots.toFinset
  have hxne (x : ℂ) (hx : x ∈ S) : x ≠ 0 := by
    have hPne : P ≠ 0 := by
      intro hz
      simp [hz] at hP
    have hroot := (mem_roots hPne).mp (Multiset.mem_toFinset.mp hx)
    intro hz
    rw [hz, IsRoot.def, ← coeff_zero_eq_eval_zero, hP] at hroot
    exact one_ne_zero hroot
  have hfactor : P = C P.leadingCoeff * ∏ x ∈ S, (X - C x) := by
    calc
      P = C P.leadingCoeff * (P.roots.map (X - C ·)).prod :=
        (IsAlgClosed.splits P).eq_prod_roots
      _ = _ := by
        congr 1
        simp only [S, Finset.prod, Multiset.toFinset_val, (Polynomial.nodup_roots hsep).dedup]
  have hfactors : (∏ x ∈ S, (X - C x)) =
      ∏ x ∈ S, C (-x) * (1 - C x⁻¹ * X) := by
    apply Finset.prod_congr rfl
    intro x hx
    rw [show X - C x = C (-x) * (1 - C x⁻¹ * X) by
      rw [mul_sub, ← mul_assoc, ← C_mul]
      simp only [neg_mul, mul_inv_cancel₀ (hxne x hx), C_neg, C_1, mul_one, neg_mul,
        one_mul]
      ring]
  have hrewrite : P =
      C (P.leadingCoeff * ∏ x ∈ S, -x) *
        ∏ x ∈ S, (1 - C x⁻¹ * X) := by
    calc
      P = C P.leadingCoeff * ∏ x ∈ S, (X - C x) := hfactor
      _ = _ := by
        rw [hfactors]
        rw [Finset.prod_mul_distrib, ← map_prod, ← mul_assoc, ← C_mul]
  have hconstant : P.leadingCoeff * ∏ x ∈ S, -x = 1 := by
    have h := congrArg (fun Q : ℂ[X] => Q.eval 0) hrewrite
    simpa only [← coeff_zero_eq_eval_zero, hP, eval_mul, eval_C, eval_prod, eval_sub,
      eval_one, eval_X, mul_zero, sub_zero, Finset.prod_const_one, mul_one] using h.symm
  calc
    P = C (P.leadingCoeff * ∏ x ∈ S, -x) *
        ∏ x ∈ S, (1 - C x⁻¹ * X) := hrewrite
    _ = ∏ x ∈ S, (1 - C x⁻¹ * X) := by rw [hconstant, C_1, one_mul]
    _ = ∏ a ∈ reciprocalRootParameters P, (1 - C a * X) := by
      symm
      exact Finset.prod_image (fun x hx y hy hxy => inv_injective hxy)

end Langlands.RankinSelberg
