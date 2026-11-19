import Langlands.Representation.Archimedean.RealCompactPolynomialFullBraid
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Interpolation of the compact braid corner expressions -/

noncomputable section
set_option autoImplicit false

namespace Langlands.Archimedean.RealCompactPolynomialCornerInterpolation

open Polynomial RealCompactPolynomialFullBraid RealCompactPolynomialRelations

variable {A : Type*} [Ring A] [Algebra ℂ A]

private def parameter (s : ℂ) : A[X] :=
  Polynomial.X + C (algebraMap ℂ A s)

private def cornerPoly (x y z : A) (s : ℂ) : A[X] :=
  C (y * x) + parameter s * C z

private def squarePoly (x : A) (s : ℂ) : A[X] :=
  C (x * x) + parameter s * parameter s

private def leftPoly (x y z : A) : ℕ → ℂ → A[X]
  | 0, _ => 1
  | 1, s => cornerPoly x y z (s + 1)
  | a + 2, s =>
      (cornerPoly x y z (s + 1) * cornerPoly x y z (s + 2) +
        ((a + 1 : ℂ) ^ 2) • squarePoly y (s + 1)) *
          leftPoly x y z a (s + 2)

private def rightPoly (x y z : A) : ℕ → ℂ → A[X]
  | 0, _ => 1
  | 1, s => cornerPoly x y z (s + 1)
  | a + 2, s =>
      rightPoly x y z a (s + 2) *
        (cornerPoly x y z (s + 2) * cornerPoly x y z (s + 1) +
          ((a + 1 : ℂ) ^ 2) • squarePoly x (s + 1))

private def evaluate (t : ℂ) : A[X] →ₐ[ℂ] A :=
  { eval₂RingHom' (RingHom.id A) (algebraMap ℂ A t)
      (fun a => (Algebra.commutes t a).symm) with
    commutes' := fun _ => eval₂_C _ _ }

private theorem evaluate_C (t : ℂ) (x : A) : evaluate t (C x) = x := by
  change eval₂ (RingHom.id A) (algebraMap ℂ A t) (C x) = x
  exact eval₂_C _ _

private theorem evaluate_X (t : ℂ) : evaluate t (Polynomial.X : A[X]) = algebraMap ℂ A t := by
  change eval₂ (RingHom.id A) (algebraMap ℂ A t) Polynomial.X = _
  exact eval₂_X _ _

private theorem evaluate_corner (x y z : A) (s t : ℂ) :
    evaluate t (cornerPoly x y z s) = corner x y z (t + s) := by
  simp only [cornerPoly, parameter, corner, map_add, map_mul, evaluate_C, evaluate_X,
    Algebra.smul_def]

private theorem evaluate_square (x : A) (s t : ℂ) :
    evaluate t (squarePoly x s) = x * x + algebraMap ℂ A ((t + s) ^ 2) := by
  simp only [squarePoly, parameter, map_add, map_mul, evaluate_C, evaluate_X, pow_two]

private theorem evaluate_left (x y z : A) (t : ℂ) (a : ℕ) (s : ℂ) :
    evaluate t (leftPoly x y z a s) = normalLeft x y z a (t + s) := by
  induction a using Nat.twoStepInduction generalizing s with
  | zero => simp [leftPoly, normalLeft]
  | one => simp [leftPoly, normalLeft, evaluate_corner, add_assoc]
  | more a ih _ =>
      simp only [leftPoly, normalLeft, map_mul, map_add, map_smul, evaluate_corner,
        evaluate_square, ih, add_assoc]

private theorem evaluate_right (x y z : A) (t : ℂ) (a : ℕ) (s : ℂ) :
    evaluate t (rightPoly x y z a s) = normalRight x y z a (t + s) := by
  induction a using Nat.twoStepInduction generalizing s with
  | zero => simp [rightPoly, normalRight]
  | one => simp [rightPoly, normalRight, evaluate_corner, add_assoc]
  | more a ih _ =>
      simp only [rightPoly, normalRight, map_mul, map_add, map_smul, evaluate_corner,
        evaluate_square, ih, add_assoc]

private def Top (p : A[X]) (n : ℕ) (c : A) : Prop :=
  p.natDegree ≤ n ∧ p.coeff n = c

omit [Algebra ℂ A] in
private theorem Top.mul {p q : A[X]} {n m : ℕ} {u v : A}
    (hp : Top p n u) (hq : Top q m v) : Top (p * q) (n + m) (u * v) :=
  ⟨natDegree_mul_le.trans (Nat.add_le_add hp.1 hq.1),
    (coeff_mul_add_eq_of_natDegree_le hp.1 hq.1).trans (by rw [hp.2, hq.2])⟩

omit [Algebra ℂ A] in
private theorem Top.add {p q : A[X]} {n : ℕ} {u v : A}
    (hp : Top p n u) (hq : Top q n v) : Top (p + q) n (u + v) :=
  ⟨(natDegree_add_le p q).trans (max_le hp.1 hq.1), by rw [coeff_add, hp.2, hq.2]⟩

private theorem Top.smul {p : A[X]} {n : ℕ} {u : A} (hp : Top p n u) (c : ℂ) :
    Top (c • p) n (c • u) := by
  refine ⟨natDegree_le_iff_coeff_eq_zero.mpr ?_, by rw [coeff_smul, hp.2]⟩
  intro k hk
  rw [coeff_smul, coeff_eq_zero_of_natDegree_lt (hp.1.trans_lt hk), smul_zero]

omit [Algebra ℂ A] in
private theorem top_constant (x : A) (n : ℕ) (hn : n ≠ 0) : Top (C x) n 0 :=
  ⟨by simp, coeff_C_of_ne_zero hn⟩

private theorem top_parameter (s : ℂ) : Top (parameter s : A[X]) 1 1 := by
  simpa [parameter] using
    (show Top (Polynomial.X : A[X]) 1 1 from ⟨natDegree_X_le, coeff_X_one⟩).add
      (top_constant (algebraMap ℂ A s) 1 (by decide))

private theorem top_corner (x y z : A) (s : ℂ) : Top (cornerPoly x y z s) 1 z := by
  have hz : Top (C z) 0 z := ⟨by simp, coeff_C_zero⟩
  simpa [cornerPoly] using (top_constant (y * x) 1 (by decide)).add ((top_parameter s).mul hz)

private theorem top_square (x : A) (s : ℂ) : Top (squarePoly x s) 2 1 := by
  simpa [squarePoly] using
    (top_constant (x * x) 2 (by decide)).add
      ((top_parameter (A := A) s).mul (top_parameter s))

private theorem factor_commute (z : A) (a : ℕ) : Commute z (factor z a) := by
  induction a using Nat.twoStepInduction with
  | zero => simp [factor]
  | one => exact Commute.refl z
  | more a ih _ =>
      rw [factor_add_two]
      exact (((Commute.refl z).mul_right (Commute.refl z)).add_right
        ((Algebra.commutes ((a + 1 : ℂ) ^ 2) z).symm)).mul_right ih

private theorem top_left (x y z : A) (a : ℕ) (s : ℂ) :
    Top (leftPoly x y z a s) a (factor z a) := by
  induction a using Nat.twoStepInduction generalizing s with
  | zero => simp [leftPoly, factor, Top]
  | one => exact top_corner x y z (s + 1)
  | more a ih _ =>
      rw [leftPoly, factor_add_two]
      simpa [Nat.add_comm, Algebra.algebraMap_eq_smul_one] using
        (((top_corner x y z (s + 1)).mul (top_corner x y z (s + 2))).add
          ((top_square y (s + 1)).smul ((a + 1 : ℂ) ^ 2))).mul (ih (s + 2))

private theorem top_right (x y z : A) (a : ℕ) (s : ℂ) :
    Top (rightPoly x y z a s) a (factor z a) := by
  induction a using Nat.twoStepInduction generalizing s with
  | zero => simp [rightPoly, factor, Top]
  | one => exact top_corner x y z (s + 1)
  | more a ih _ =>
      rw [rightPoly, factor_add_two]
      have hcomm : Commute (factor z a)
          (z * z + algebraMap ℂ A ((a + 1 : ℂ) ^ 2)) :=
        (((factor_commute z a).symm).mul_right ((factor_commute z a).symm)).add_right
          ((Algebra.commutes ((a + 1 : ℂ) ^ 2) (factor z a)).symm)
      rw [← hcomm.eq]
      simpa [Algebra.algebraMap_eq_smul_one] using
        (ih (s + 2)).mul (((top_corner x y z (s + 2)).mul (top_corner x y z (s + 1))).add
          ((top_square x (s + 1)).smul ((a + 1 : ℂ) ^ 2)))

private theorem polynomial_eq_zero {a : ℕ} (p : A[X]) (hdeg : p.natDegree < a)
    (hroots : ∀ b : Fin a, evaluate (b.val : ℂ) p = 0) : p = 0 := by
  classical
  ext n
  rw [coeff_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro φ
  let q : ℂ[X] := ∑ k ∈ Finset.range a, monomial k (φ (p.coeff k))
  have hq (k : ℕ) : q.coeff k = φ (p.coeff k) := by
    by_cases hk : k < a
    · simp [q, coeff_monomial, Finset.mem_range.mpr hk]
    · have hz : p.coeff k = 0 := coeff_eq_zero_of_natDegree_lt (hdeg.trans_le (le_of_not_gt hk))
      simp [q, coeff_monomial, hk, hz]
  have hqdeg : q.natDegree < a := by
    by_contra! h
    have hcoeff : q.coeff q.natDegree = 0 := by
      rw [hq, coeff_eq_zero_of_natDegree_lt (hdeg.trans_le h), map_zero]
    have hzero : q = 0 := leadingCoeff_eq_zero.mp hcoeff
    have ha : a ≤ 0 := by simpa [hzero] using h
    exact (Nat.zero_le _ |>.trans_lt hdeg |>.not_ge) ha
  have heval (b : Fin a) : q.eval (b.val : ℂ) = 0 := by
    have he : evaluate (b.val : ℂ) p =
        ∑ k ∈ Finset.range a, (b.val : ℂ) ^ k • p.coeff k := by
      change eval₂ (RingHom.id A) _ _ = _
      rw [eval₂_eq_sum_range' _ hdeg]
      simp only [RingHom.id_apply, ← map_pow, Algebra.smul_def]
      exact Finset.sum_congr rfl fun k _ => (Algebra.commutes ((b.val : ℂ) ^ k) (p.coeff k)).symm
    have h := congrArg φ (he.symm.trans (hroots b))
    simpa [q, mul_comm, eval_finsetSum] using h
  have hzero : q = 0 :=
    eq_zero_of_natDegree_lt_card_of_eval_eq_zero q
      (f := fun b : Fin a => (b.val : ℂ))
      (fun _ _ hab => Fin.ext (Nat.cast_injective hab)) heval (by simpa using hqdeg)
  rw [← hq, hzero, coeff_zero]

/-- The first `a` natural values determine equality of the two corner expressions. -/
theorem normal_eq_of_small {x y z : A} (a : ℕ)
    (h : ∀ b : Fin a, normalLeft x y z a (b.val : ℂ) = normalRight x y z a (b.val : ℂ))
    (t : ℂ) : normalLeft x y z a t = normalRight x y z a t := by
  by_cases ha : a = 0
  · simp [ha, normalLeft, normalRight]
  let p := leftPoly x y z a 0 - rightPoly x y z a 0
  have hp (k : ℕ) (hk : a ≤ k) : p.coeff k = 0 := by
    rcases eq_or_lt_of_le hk with he | hlt
    · subst k
      rw [show p.coeff a = (leftPoly x y z a 0).coeff a -
        (rightPoly x y z a 0).coeff a from coeff_sub ..,
        (top_left x y z a 0).2, (top_right x y z a 0).2, sub_self]
    · rw [show p.coeff k = (leftPoly x y z a 0).coeff k -
        (rightPoly x y z a 0).coeff k from coeff_sub ..,
        coeff_eq_zero_of_natDegree_lt ((top_left x y z a 0).1.trans_lt hlt),
        coeff_eq_zero_of_natDegree_lt ((top_right x y z a 0).1.trans_lt hlt), sub_self]
  have hdeg : p.natDegree < a := by
    by_contra! hge
    have hzero : p = 0 := leadingCoeff_eq_zero.mp (hp _ hge)
    simp [hzero, ha] at hge
  have hzero := polynomial_eq_zero p hdeg (fun b => by
    simp [p, evaluate_left, evaluate_right, h b])
  have he := congrArg (evaluate (A := A) t) (sub_eq_zero.mp hzero)
  simpa [evaluate_left, evaluate_right] using he

end Langlands.Archimedean.RealCompactPolynomialCornerInterpolation
