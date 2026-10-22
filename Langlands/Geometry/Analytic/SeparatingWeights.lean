import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finsupp.Basic
import Mathlib.Tactic.Ring

/-! # Actual integer weights separating finitely many monomials -/

namespace Langlands.Analytic

open scoped BigOperators

/-- Base-power weight, with coordinate zero of weight one. -/
def baseWeight {n : ℕ} (b : ℕ) (d : Fin n → ℕ) : ℕ :=
  ∑ i : Fin n, d i * b ^ (i : ℕ)

theorem baseWeight_succ {n : ℕ} (b : ℕ) (d : Fin (n + 1) → ℕ) :
    baseWeight b d = d 0 + b * baseWeight b (fun i : Fin n => d i.succ) := by
  simp only [baseWeight, Fin.sum_univ_succ, Fin.val_zero, pow_zero, mul_one,
    Fin.val_succ, pow_succ]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Bounded digits are recovered from their base-power weight. -/
theorem baseWeight_injective_of_lt {n : ℕ} {b : ℕ} (hb : 0 < b)
    {d e : Fin n → ℕ} (hd : ∀ i, d i < b) (he : ∀ i, e i < b)
    (h : baseWeight b d = baseWeight b e) : d = e := by
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
    rw [baseWeight_succ, baseWeight_succ] at h
    have h0 : d 0 = e 0 := by
      have hm := congrArg (fun k => k % b) h
      simpa only [Nat.add_mod, Nat.mul_mod_right, add_zero,
        Nat.mod_eq_of_lt (hd 0), Nat.mod_eq_of_lt (he 0)] using hm
    have ht : baseWeight b (fun i : Fin n => d i.succ) =
        baseWeight b (fun i : Fin n => e i.succ) := by
      rw [h0] at h
      exact Nat.eq_of_mul_eq_mul_left hb (Nat.add_left_cancel h)
    have hi := ih (fun i => hd i.succ) (fun i => he i.succ) ht
    funext i
    refine Fin.cases h0 (fun j => ?_) i
    exact congrFun hi j

/-- A concrete base larger than every coordinate in a finite set. -/
def separatingBase {n : ℕ} (S : Finset (Fin n →₀ ℕ)) : ℕ :=
  S.sup (fun d => Finset.univ.sup fun i : Fin n => d i) + 2

theorem separatingBase_two_le {n : ℕ} (S : Finset (Fin n →₀ ℕ)) :
    2 ≤ separatingBase S := Nat.le_add_left 2 _

theorem lt_separatingBase {n : ℕ} (S : Finset (Fin n →₀ ℕ))
    {d : Fin n →₀ ℕ} (hd : d ∈ S) (i : Fin n) :
    d i < separatingBase S := by
  have h1 : d i ≤ Finset.univ.sup (fun j : Fin n => d j) :=
    Finset.le_sup (Finset.mem_univ i)
  have h2 : Finset.univ.sup (fun j : Fin n => d j) ≤
      S.sup (fun e => Finset.univ.sup fun j : Fin n => e j) :=
    Finset.le_sup (f := fun e : Fin n →₀ ℕ =>
      Finset.univ.sup fun j : Fin n => e j) hd
  dsimp [separatingBase]
  omega

theorem baseWeight_injOn {n : ℕ} (S : Finset (Fin n →₀ ℕ)) :
    Set.InjOn (fun d : Fin n →₀ ℕ => baseWeight (separatingBase S) d) (S : Set _) := by
  intro d hd e he h
  apply DFunLike.ext
  intro i
  exact congrFun (baseWeight_injective_of_lt
    (lt_of_lt_of_le (by decide : 0 < 2) (separatingBase_two_le S))
    (lt_separatingBase S hd) (lt_separatingBase S he) h) i

/-- The constructed weights give a unique highest-weight monomial in any
nonempty finite set. No choice of a separating weight is assumed. -/
theorem exists_unique_max_baseWeight {n : ℕ} (S : Finset (Fin n →₀ ℕ))
    (hS : S.Nonempty) :
    ∃ d ∈ S, ∀ e ∈ S, e ≠ d →
      baseWeight (separatingBase S) e < baseWeight (separatingBase S) d := by
  obtain ⟨d, hd, hmax⟩ :=
    Finset.exists_max_image S (fun d => baseWeight (separatingBase S) d) hS
  refine ⟨d, hd, fun e he hne => ?_⟩
  apply lt_of_le_of_ne (hmax e he)
  intro h
  exact hne (baseWeight_injOn S he hd h)

end Langlands.Analytic
