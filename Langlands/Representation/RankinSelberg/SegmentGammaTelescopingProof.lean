import Langlands.Representation.RankinSelberg.SegmentGammaTelescopingStatement
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fin.Rev

noncomputable section

namespace Langlands.RankinSelberg.SegmentGammaTelescoping

open Polynomial LocalFactor

@[simp] theorem linearFactor_coeff_zero (a : ℂˣ) :
    (linearFactor a).coeff 0 = 1 := by simp [linearFactor]

theorem linearFactor_ne_zero (a : ℂˣ) : linearFactor a ≠ 0 := by
  intro h
  have := congrArg (fun P : ℂ[X] => P.coeff 0) h
  simp at this

/-- Reciprocal reflection of one linear factor, with its explicit Laurent unit. -/
theorem reflected_linearFactor (δ b : ℂˣ) :
    RationalReflection.subst δ
        (algebraMap ℂ[X] (RatFunc ℂ) (linearFactor b)) =
      (rationalEpsilonMonomial (-(b * δ)) (-1) : RatFunc ℂ) *
        algebraMap ℂ[X] (RatFunc ℂ) (linearFactor ((b * δ)⁻¹)) := by
  rw [RationalReflection.subst_polynomial]
  simp only [linearFactor, map_sub, map_one, map_mul, aeval_C, aeval_X,
    RatFunc.algebraMap_X, RatFunc.algebraMap_C,
    coe_rationalEpsilonMonomial, Units.val_neg, Units.val_mul,
    Units.val_inv_eq_inv_val, zpow_neg_one, RationalReflection.reflectedVariable,
    RatFunc.algebraMap_eq_C, map_neg, map_inv₀]
  have hC : RatFunc.C (b : ℂ) ≠ 0 := (_root_.map_ne_zero _).mpr b.ne_zero
  have hD : RatFunc.C (δ : ℂ) ≠ 0 := (_root_.map_ne_zero _).mpr δ.ne_zero
  field_simp [RatFunc.X_ne_zero]
  ring


private def linearUnit (a : ℂˣ) : RationalFunctionsˣ :=
  Units.mk0 (algebraMap ℂ[X] RationalFunctions (linearFactor a))
    (by
      intro h
      exact linearFactor_ne_zero a
        (RatFunc.algebraMap_injective ℂ (by simpa using h)))

private def reflectUnit (δ : ℂˣ) : RationalFunctionsˣ →* RationalFunctionsˣ :=
  Units.map (RationalReflection.subst δ).toMonoidHom

private theorem reflected_linearUnit (δ b : ℂˣ) :
    reflectUnit δ (linearUnit b) = rationalEpsilonMonomial (-(b * δ)) (-1) *
      linearUnit ((b * δ)⁻¹) := by
  apply Units.ext
  simpa [reflectUnit, linearUnit] using reflected_linearFactor δ b

private theorem monomial_mul (c d : ℂˣ) (e f : ℤ) :
    rationalEpsilonMonomial (c * d) (e + f) =
      rationalEpsilonMonomial c e * rationalEpsilonMonomial d f := by
  simp only [rationalEpsilonMonomial, map_mul, zpow_add]
  ac_rfl

private theorem monomial_inv (c : ℂˣ) (e : ℤ) :
    rationalEpsilonMonomial c⁻¹ (-e) = (rationalEpsilonMonomial c e)⁻¹ := by
  simp [rationalEpsilonMonomial, mul_comm]

private theorem monomial_div (c d : ℂˣ) (e f : ℤ) :
    rationalEpsilonMonomial (c / d) (e - f) =
      rationalEpsilonMonomial c e / rationalEpsilonMonomial d f := by
  rw [div_eq_mul_inv, sub_eq_add_neg, monomial_mul, monomial_inv, div_eq_mul_inv]

private def Related (A B : RationalFunctionsˣ) : Prop :=
  ∃ (c : ℂˣ) (e : ℤ), A = rationalEpsilonMonomial c e * B

private theorem related_refl (A : RationalFunctionsˣ) : Related A A := by
  refine ⟨1, 0, ?_⟩
  simp [rationalEpsilonMonomial]

private theorem related_symm {A B : RationalFunctionsˣ} (h : Related A B) :
    Related B A := by
  obtain ⟨c, e, h⟩ := h
  refine ⟨c⁻¹, -e, ?_⟩
  rw [monomial_inv, h, inv_mul_cancel_left]

private theorem related_trans {A B C : RationalFunctionsˣ}
    (h : Related A B) (h' : Related B C) : Related A C := by
  obtain ⟨c, e, h⟩ := h
  obtain ⟨d, f, h'⟩ := h'
  refine ⟨c * d, e + f, ?_⟩
  rw [monomial_mul, h, h', mul_assoc]

private theorem related_mul {A B C D : RationalFunctionsˣ}
    (h : Related A B) (h' : Related C D) : Related (A * C) (B * D) := by
  obtain ⟨c, e, h⟩ := h
  obtain ⟨d, f, h'⟩ := h'
  refine ⟨c * d, e + f, ?_⟩
  rw [monomial_mul, h, h']
  ac_rfl

private theorem related_div {A B C D : RationalFunctionsˣ}
    (h : Related A B) (h' : Related C D) : Related (A / C) (B / D) := by
  obtain ⟨c, e, h⟩ := h
  obtain ⟨d, f, h'⟩ := h'
  refine ⟨c / d, e - f, ?_⟩
  rw [monomial_div, h, h']
  simp only [div_eq_mul_inv, mul_inv_rev]
  ac_rfl

private theorem related_prod {ι : Type*} (s : Finset ι)
    (f g : ι → RationalFunctionsˣ) (h : ∀ i ∈ s, Related (f i) (g i)) :
    Related (∏ i ∈ s, f i) (∏ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using related_refl 1
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact related_mul (h i (Finset.mem_insert_self _ _))
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

private theorem reflected_shift (a t : ℂˣ) (k : ℤ) :
    Related (reflectUnit (t ^ 2) (linearUnit (a⁻¹ * t⁻¹ ^ k)))
      (linearUnit (a * t ^ (k - 2))) := by
  rw [reflected_linearUnit]
  have harg : ((a⁻¹ * t⁻¹ ^ k) * t ^ 2)⁻¹ = a * t ^ (k - 2) := by
    group
    ac_rfl
  rw [harg]
  exact ⟨_, -1, rfl⟩

private theorem column_telescoping (a t : ℂˣ) (k : ℤ) (m : ℕ) :
    (∏ i : Fin (m + 1),
      linearUnit (a * t ^ (k - 2 * (i.val : ℤ))) /
        linearUnit (a * t ^ (k - 2 * (i.val : ℤ) - 2))) =
      linearUnit (a * t ^ k) /
        linearUnit (a * t ^ (k - 2 * ((m : ℤ) + 1))) := by
  let f (i : ℕ) := linearUnit (a * t ^ (k - 2 * (i : ℤ)))
  have hexp (i : ℕ) : k - 2 * (i : ℤ) - 2 = k - 2 * ((i + 1 : ℕ) : ℤ) := by
    push_cast
    ring
  simp_rw [hexp]
  change (∏ i : Fin (m + 1), f i.val / f (i.val + 1)) = _
  rw [Fin.prod_univ_eq_prod_range (fun i => f i / f (i + 1)) (m + 1)]
  rw [Finset.prod_range_div']
  simp [f]

private def fullUnit (a t : ℂˣ) (m n : ℕ) : RationalFunctionsˣ :=
  ∏ i : Fin (m + 1), ∏ j : Fin (n + 1),
    linearUnit (a * t ^ blockExponent m n i.val j.val)

private def boundaryUnit (a t : ℂˣ) (m n : ℕ) : RationalFunctionsˣ :=
  ∏ j : Fin (n + 1), linearUnit (a * t ^ blockExponent m n 0 j.val)

private def shiftedUnit (a t : ℂˣ) (m n : ℕ) : RationalFunctionsˣ :=
  ∏ i : Fin (m + 1), ∏ j : Fin (n + 1),
    linearUnit (a * t ^ (blockExponent m n i.val j.val - 2))

private def endpointUnit (a t : ℂˣ) (m n : ℕ) : RationalFunctionsˣ :=
  ∏ j : Fin (n + 1), linearUnit (a * t ^ ((n : ℤ) - m - 2 - 2 * j.val))

private theorem reflected_full (a t : ℂˣ) (m n : ℕ) :
    Related (reflectUnit (t ^ 2) (fullUnit a⁻¹ t⁻¹ m n))
      (shiftedUnit a t m n) := by
  simp only [fullUnit, shiftedUnit, map_prod]
  apply related_prod
  intro i _
  apply related_prod
  intro j _
  exact reflected_shift a t _

private theorem full_telescoping (a t : ℂˣ) (m n : ℕ) :
    fullUnit a t m n / shiftedUnit a t m n =
      boundaryUnit a t m n / endpointUnit a t m n := by
  simp only [fullUnit, shiftedUnit, boundaryUnit, endpointUnit,
    ← Finset.prod_div_distrib]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro j _
  have hcol := column_telescoping a t ((m : ℤ) + n - 2 * j.val) m
  have hinput (i : Fin (m + 1)) :
      blockExponent m n i.val j.val = (m : ℤ) + n - 2 * j.val - 2 * i.val := by
    simp only [blockExponent]
    ring
  have hstart : blockExponent m n 0 j.val = (m : ℤ) + n - 2 * j.val := by
    simp [blockExponent]
  have hend : (m : ℤ) + n - 2 * j.val - 2 * ((m : ℤ) + 1) =
      (n : ℤ) - m - 2 - 2 * j.val := by ring
  simpa only [hinput, hstart, hend] using hcol

private theorem reflected_boundary_shift (a t : ℂˣ) (k : ℤ) :
    Related (reflectUnit (t ^ 2) (linearUnit (a⁻¹ * t ^ k)))
      (linearUnit (a * t ^ (-k - 2))) := by
  rw [reflected_linearUnit]
  have harg : ((a⁻¹ * t ^ k) * t ^ 2)⁻¹ = a * t ^ (-k - 2) := by
    group
    ac_rfl
  rw [harg]
  exact ⟨_, -1, rfl⟩

private theorem boundary_reversal (a t : ℂˣ) (m n : ℕ) :
    (∏ j : Fin (n + 1),
      linearUnit (a * t ^ (-blockExponent m n 0 j.val - 2))) =
      endpointUnit a t m n := by
  unfold endpointUnit
  apply Fintype.prod_equiv (Fin.revPerm : Fin (n + 1) ≃ Fin (n + 1))
  intro j
  congr 3
  simp only [blockExponent, Nat.cast_zero, mul_zero, sub_zero,
    Fin.revPerm_apply, Fin.val_rev]
  have hj : j.val ≤ n := Nat.le_of_lt_succ j.isLt
  push_cast [Nat.cast_sub hj]
  ring

private theorem reflected_boundary (a t : ℂˣ) (m n : ℕ) :
    Related (reflectUnit (t ^ 2) (boundaryUnit a⁻¹ t m n))
      (endpointUnit a t m n) := by
  rw [← boundary_reversal]
  simp only [boundaryUnit, map_prod]
  apply related_prod
  intro j _
  exact reflected_boundary_shift a t _

private theorem single_parameter (a t : ℂˣ) (m n : ℕ) :
    Related
      (boundaryUnit a t m n / reflectUnit (t ^ 2) (boundaryUnit a⁻¹ t m n))
      (fullUnit a t m n / reflectUnit (t ^ 2) (fullUnit a⁻¹ t⁻¹ m n)) := by
  have hfull := related_div (related_refl (fullUnit a t m n))
    (reflected_full a t m n)
  rw [full_telescoping] at hfull
  exact related_trans (related_div (related_refl _) (reflected_boundary a t m n))
    (related_symm hfull)

private theorem coe_fullUnit (a t : ℂˣ) (m n : ℕ) :
    (fullUnit a t m n : RationalFunctions) =
      algebraMap ℂ[X] RationalFunctions (fullPolynomial a t m n) := by
  simp [fullUnit, fullPolynomial, linearUnit, map_prod]

private theorem coe_boundaryUnit (a t : ℂˣ) (m n : ℕ) :
    (boundaryUnit a t m n : RationalFunctions) =
      algebraMap ℂ[X] RationalFunctions (boundaryPolynomial a t m n) := by
  simp [boundaryUnit, boundaryPolynomial, linearUnit, map_prod]

private theorem coe_reflectUnit (δ : ℂˣ) (U : RationalFunctionsˣ) :
    (reflectUnit δ U : RationalFunctions) = RationalReflection.subst δ (U : RationalFunctions) := rfl

end Langlands.RankinSelberg.SegmentGammaTelescoping

namespace Langlands.RankinSelberg

open SegmentGammaTelescoping

/-- The full centered rectangle cancels to its first-row reflected ratio. -/
theorem segmentGammaTelescoping : SegmentGammaTelescopingStatement := by
  classical
  intro A t m n
  obtain ⟨c, e, h⟩ := related_prod A
    (fun a => boundaryUnit a t m n /
      reflectUnit (t ^ 2) (boundaryUnit a⁻¹ t m n))
    (fun a => fullUnit a t m n /
      reflectUnit (t ^ 2) (fullUnit a⁻¹ t⁻¹ m n))
    (fun a _ => single_parameter a t m n)
  refine ⟨⟨c, e, ?_⟩⟩
  have h' := congrArg (fun U : RationalFunctionsˣ => (U : RationalFunctions)) h
  simp only [Units.coe_prod, Units.val_div_eq_div_val, Units.val_mul,
    coe_reflectUnit, coe_boundaryUnit, coe_fullUnit,
    coe_rationalEpsilonMonomial, RatFunc.algebraMap_eq_C] at h'
  simpa only [map_prod, mul_div_assoc, ← Finset.prod_div_distrib] using h'

end Langlands.RankinSelberg
