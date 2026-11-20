import Langlands.Representation.Archimedean.RealStandardEllipticCartanNumerator
import Langlands.Representation.Archimedean.RealBlockFourierFinite

/-! # Rigidity of the scalar in the finite Cartan numerator -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean.RealStandardEllipticCartan

open RealBlockFourierFinite

private def commonAngle {r s : ℕ} (θ : ℝ) : Coordinates r s :=
  ((fun _ => Multiplicative.ofAdd (0, θ)), 1)

private def angleProduct {r : ℕ} (w : Fin r → ℤ) (θ : ℝ) : ℂ :=
  ∏ i, (expMode (w i) θ - expMode (-(w i)) θ)

private theorem complexTerm_commonAngle (m : ℤ) (t : ℂ) (θ : ℝ) :
    complexTerm (m, t) (Multiplicative.ofAdd (0, θ)) = expMode m θ := by
  change Complex.exp (((0 : ℝ) : ℂ) * (2 * t) + (θ : ℂ) * (Complex.I * (m : ℂ))) = _
  rw [Complex.ofReal_zero, zero_mul, zero_add, expMode]
  congr 1
  ring

private def permutationCount (r s : ℕ) : ℂ :=
  (Fintype.card (Equiv.Perm (Fin r)) : ℂ) * (Fintype.card (Equiv.Perm (Fin s)) : ℂ)

private theorem permutationCount_ne_zero (r s : ℕ) : permutationCount r s ≠ 0 :=
  mul_ne_zero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
    (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

private theorem numerator_commonAngle {r s : ℕ} (p : Parameters r s) (θ : ℝ) :
    numerator p (commonAngle θ) = permutationCount r s * angleProduct (fun i => (p.1 i).1) θ := by
  rw [numerator_apply]
  change (∑ π : Equiv.Perm (Fin r), ∑ σ : Equiv.Perm (Fin s),
    (∏ i, (complexTerm ((p.1 (π i)).1, (p.1 (π i)).2) (Multiplicative.ofAdd (0, θ)) -
      complexTerm (-(p.1 (π i)).1, (p.1 (π i)).2) (Multiplicative.ofAdd (0, θ)))) *
        ∏ j, realTerm (p.2 (σ j)) 1) = _
  simp_rw [complexTerm_commonAngle, map_one, Finset.prod_const_one, mul_one]
  have hp (π : Equiv.Perm (Fin r)) :
      (∏ i, (expMode (p.1 (π i)).1 θ - expMode (-(p.1 (π i)).1) θ)) =
        angleProduct (fun i => (p.1 i).1) θ :=
    Equiv.prod_comp π (fun i => expMode (p.1 i).1 θ - expMode (-(p.1 i).1) θ)
  simp_rw [hp]
  simp [permutationCount, Finset.sum_const, nsmul_eq_mul, mul_assoc]

private def orientedWeight {r : ℕ} (w : Fin r → ℤ) (e : Fin r → Bool) (i : Fin r) : ℤ :=
  if e i then -w i else w i

private def orientedSign {r : ℕ} (e : Fin r → Bool) : ℂ :=
  ∏ i, if e i then -1 else 1

private theorem prod_expMode {r : ℕ} (w : Fin r → ℤ) (θ : ℝ) :
    (∏ i, expMode (w i) θ) = expMode (∑ i, w i) θ := by
  simp only [expMode, ← Complex.exp_sum, Int.cast_sum, Finset.sum_mul]

private theorem angleProduct_expansion {r : ℕ} (w : Fin r → ℤ) (θ : ℝ) :
    angleProduct w θ = ∑ e : Fin r → Bool,
      orientedSign e * expMode (∑ i, orientedWeight w e i) θ := by
  let f (i : Fin r) (b : Bool) : ℂ :=
    (if b then -1 else 1) * expMode (if b then -w i else w i) θ
  have h (e : Fin r → Bool) : (∏ i, f i (e i)) =
      orientedSign e * expMode (∑ i, orientedWeight w e i) θ := by
    dsimp only [f, orientedSign]
    rw [Finset.prod_mul_distrib]
    congr 1
    exact prod_expMode (orientedWeight w e) θ
  simp_rw [← h]
  rw [← Fintype.prod_sum f]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp [f, sub_eq_add_neg, add_comm]

private theorem coeff_sum {ι : Type*} (s : Finset ι) (F : ι → ℝ → ℂ)
    (hF : ∀ i ∈ s, Continuous (F i)) (k : ℤ) :
    coeff k (fun θ => ∑ i ∈ s, F i θ) = ∑ i ∈ s, coeff k (F i) := by
  unfold coeff
  simp_rw [Finset.sum_mul]
  exact intervalIntegral.integral_finsetSum fun i hi => intervalIntegrable_coeff (hF i hi) k _ _

private theorem coeff_angleProduct_expansion {r : ℕ} (w : Fin r → ℤ) (k : ℤ) :
    coeff k (angleProduct w) = ∑ e : Fin r → Bool,
      orientedSign e * (if (∑ i, orientedWeight w e i) = k then 2 * (Real.pi : ℂ) else 0) := by
  let F (e : Fin r → Bool) : ℝ → ℂ := orientedSign e • expMode (∑ i, orientedWeight w e i)
  have hF : ∀ e ∈ (Finset.univ : Finset (Fin r → Bool)), Continuous (F e) :=
    fun e _ => (continuous_expMode (∑ i, orientedWeight w e i)).const_smul _
  rw [show angleProduct w = (fun θ => ∑ e, F e θ) from funext (angleProduct_expansion w),
    coeff_sum _ F hF]
  refine Finset.sum_congr rfl fun e _ => ?_
  change coeff k (orientedSign e • expMode (∑ i, orientedWeight w e i)) = _
  rw [coeff_smul, coeff_expMode]

private theorem orientedWeight_le {r : ℕ} {w : Fin r → ℤ} (hw : ∀ i, 0 < w i)
    (e : Fin r → Bool) (i : Fin r) : orientedWeight w e i ≤ w i := by
  unfold orientedWeight
  split_ifs
  · linarith [hw i]
  · rfl

private theorem orientedWeight_sum_eq {r : ℕ} {w : Fin r → ℤ} (hw : ∀ i, 0 < w i)
    (e : Fin r → Bool) : (∑ i, orientedWeight w e i) = ∑ i, w i ↔ e = fun _ => false := by
  constructor
  · intro he
    funext i
    by_contra hi
    have ht : e i = true := Bool.eq_true_of_ne_false hi
    have hs : (∑ j, orientedWeight w e j) < ∑ j, w j :=
      Finset.sum_lt_sum (fun j _ => orientedWeight_le hw e j)
        ⟨i, Finset.mem_univ i, by simpa [orientedWeight, ht] using neg_lt_self (hw i)⟩
    exact hs.ne he
  · rintro rfl
    simp [orientedWeight]

private theorem coeff_angleProduct_of_total_le {r : ℕ} {w : Fin r → ℤ}
    (hw : ∀ i, 0 < w i) {k : ℤ} (hk : (∑ i, w i) ≤ k) :
    coeff k (angleProduct w) = if k = (∑ i, w i) then 2 * (Real.pi : ℂ) else 0 := by
  rw [coeff_angleProduct_expansion]
  by_cases he : k = (∑ i, w i)
  · subst k
    simp_rw [orientedWeight_sum_eq hw, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ (fun _ : Fin r => false))]
    simp [orientedSign]
  · have hne (e : Fin r → Bool) : (∑ i, orientedWeight w e i) ≠ k :=
      ne_of_lt ((Finset.sum_le_sum fun i _ => orientedWeight_le hw e i).trans_lt
        (lt_of_le_of_ne hk (Ne.symm he)))
    simp [he, hne]

/-- At fixed slot counts, a proportionality between two positive-weight numerators
has equal nonzero scalars and yields equality of the two numerator functions. -/
theorem scalars_eq_and_numerator_eq_of_mul_eq {r s : ℕ} {p q : Parameters r s}
    (hp : ∀ i, 0 < (p.1 i).1) (hq : ∀ i, 0 < (q.1 i).1)
    {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ∀ x, a * numerator p x = b * numerator q x) :
    a = b ∧ numerator p = numerator q := by
  let w (i : Fin r) := (p.1 i).1
  let v (i : Fin r) := (q.1 i).1
  let m := ∑ i, w i
  let n := ∑ i, v i
  let P := permutationCount r s
  let C := 2 * (Real.pi : ℂ)
  have hC : C ≠ 0 := mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hP : P ≠ 0 := permutationCount_ne_zero r s
  have hf : (a * P) • angleProduct w = (b * P) • angleProduct v := by
    funext θ
    have he := h (commonAngle θ)
    rw [numerator_commonAngle, numerator_commonAngle] at he
    simpa only [Pi.smul_apply, smul_eq_mul, mul_assoc] using he
  have hcoeff (k : ℤ) : (a * P) * coeff k (angleProduct w) = (b * P) * coeff k (angleProduct v) := by
    simpa only [coeff_smul] using congrArg (coeff k) hf
  have hm : m ≤ n := by
    by_contra! hn
    have he := hcoeff m
    rw [coeff_angleProduct_of_total_le hp (le_refl m), coeff_angleProduct_of_total_le hq hn.le,
      ite_eq_left rfl, ite_eq_right hn.ne', mul_zero] at he
    exact (mul_ne_zero (mul_ne_zero ha hP) hC) he
  have hn : n ≤ m := by
    by_contra! hm
    have he := hcoeff n
    rw [coeff_angleProduct_of_total_le hp hm.le, coeff_angleProduct_of_total_le hq (le_refl n),
      ite_eq_right hm.ne', ite_eq_left rfl, mul_zero] at he
    exact (mul_ne_zero (mul_ne_zero hb hP) hC) he.symm
  have hmn : m = n := le_antisymm hm hn
  have he := hcoeff m
  rw [coeff_angleProduct_of_total_le hp (le_refl m), coeff_angleProduct_of_total_le hq hn,
    ite_eq_left rfl, ite_eq_left hmn] at he
  have hab : a = b := mul_right_cancel₀ hP (mul_right_cancel₀ hC he)
  subst b
  exact ⟨rfl, funext fun x => mul_left_cancel₀ ha (h x)⟩

/-- Positive-weight Cartan numerator proportionality at fixed counts determines both the
scalar and the full numerator. -/
def RealStandardEllipticCartanNumeratorScaleStatement : Prop :=
  ∀ (r s : ℕ) (p q : Parameters r s), (∀ i, 0 < (p.1 i).1) → (∀ i, 0 < (q.1 i).1) →
    ∀ a b : ℂ, a ≠ 0 → b ≠ 0 →
      (∀ x, a * numerator p x = b * numerator q x) → a = b ∧ numerator p = numerator q

theorem realStandardEllipticCartanNumeratorScale : RealStandardEllipticCartanNumeratorScaleStatement :=
  fun _ _ _ _ hp hq _ _ ha hb h => scalars_eq_and_numerator_eq_of_mul_eq hp hq ha hb h

end Langlands.Archimedean.RealStandardEllipticCartan
