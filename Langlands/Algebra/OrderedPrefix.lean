import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.End
import Mathlib.Data.Fin.Tuple.Basic

/-! # Prefix products and interleaved group products -/

namespace Langlands

section Monoid

variable {A : Type*} [Monoid A]

/-- Products of the initial segments of a finite ordered family. -/
def orderedPrefix : (r : ℕ) → (Fin r → A) → Fin (r + 1) → A
  | 0, _ => fun _ => 1
  | r + 1, f => Fin.cons 1 (fun j => f 0 * orderedPrefix r (fun i => f i.succ) j)

@[simp]
theorem orderedPrefix_zero (r : ℕ) (f : Fin r → A) :
    orderedPrefix r f 0 = 1 := by
  cases r <;> rfl

@[simp]
theorem orderedPrefix_succ (r : ℕ) (f : Fin (r + 1) → A) (j : Fin (r + 1)) :
    orderedPrefix (r + 1) f j.succ = f 0 * orderedPrefix r (fun i => f i.succ) j :=
  rfl

theorem orderedPrefix_last (r : ℕ) (f : Fin r → A) :
    orderedPrefix r f (Fin.last r) = (List.ofFn f).prod := by
  induction r with
  | zero => simp [orderedPrefix]
  | succ r ih =>
    rw [← Fin.succ_last, orderedPrefix_succ, ih, List.ofFn_succ, List.prod_cons]

theorem map_orderedPrefix {B : Type*} [Monoid B] (h : A →* B)
    (r : ℕ) (f : Fin r → A) (j : Fin (r + 1)) :
    h (orderedPrefix r f j) = orderedPrefix r (fun i => h (f i)) j := by
  induction r with
  | zero => simp [orderedPrefix]
  | succ r ih =>
    refine Fin.cases ?_ (fun j => ?_) j
    · simp
    · rw [orderedPrefix_succ, map_mul, ih, orderedPrefix_succ]

end Monoid

section Group

variable {A : Type*} [Group A]

/-- Move each interleaved constant to the far right by prefix conjugation. -/
theorem interleaved_prod_eq_prefix_conjugates (r : ℕ) (x n : Fin r → A) :
    (List.ofFn fun j => x j * n j).prod =
      (List.ofFn fun j => orderedPrefix r n j.castSucc * x j *
        (orderedPrefix r n j.castSucc)⁻¹).prod * (List.ofFn n).prod := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [List.ofFn_succ, List.prod_cons, ih (fun j => x j.succ) (fun j => n j.succ)]
    rw [List.ofFn_succ, List.prod_cons, List.ofFn_succ, List.prod_cons]
    simp only [Fin.castSucc_zero, orderedPrefix_zero, one_mul, inv_one, mul_one,
      ← Fin.succ_castSucc, orderedPrefix_succ, mul_inv_rev]
    have hconj :
        (List.ofFn fun j : Fin r =>
          n 0 * orderedPrefix r (fun i => n i.succ) j.castSucc * x j.succ *
            ((orderedPrefix r (fun i => n i.succ) j.castSucc)⁻¹ * (n 0)⁻¹)).prod =
          n 0 * (List.ofFn fun j : Fin r =>
            orderedPrefix r (fun i => n i.succ) j.castSucc * x j.succ *
              (orderedPrefix r (fun i => n i.succ) j.castSucc)⁻¹).prod * (n 0)⁻¹ := by
      simpa only [List.map_ofFn, Function.comp_def, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply, mul_assoc] using
        (map_list_prod (MulAut.conj (n 0)).toMonoidHom
          (List.ofFn fun j : Fin r =>
            orderedPrefix r (fun i => n i.succ) j.castSucc * x j.succ *
              (orderedPrefix r (fun i => n i.succ) j.castSucc)⁻¹)).symm
    rw [hconj]
    simp only [mul_assoc, inv_mul_cancel_left]

end Group

end Langlands
