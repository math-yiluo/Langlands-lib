import Mathlib.GroupTheory.Coxeter.Inversion
import Mathlib.Data.List.Count
import Mathlib.Data.List.Nodup

/-!
# Simple exchange from the Coxeter presentation

A signed action records inversion counts modulo two. The Coxeter relations
hold because the inversion sequence of a defining relation consists of two
identical halves. This supplies the exchange lemma used by the minimum-length
proof without adding an exchange hypothesis.
-/

namespace Langlands.Group.RelativeWeylIndexing

universe u v
variable {B : Type u} {W : Type v} [Group W]
variable {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

open Classical
noncomputable section

/-- Pull back by simple conjugation and toggle the value at that simple reflection. -/
def signedSimple (i : B) : Function.End (W → ZMod 2) :=
  fun f t => f (cs.simple i * t * cs.simple i) + if t = cs.simple i then 1 else 0

def signedWord (ω : List B) : Function.End (W → ZMod 2) :=
  (ω.map (signedSimple cs)).prod

private theorem count_conj (l : List W) (i : B) (t : W) :
    (l.map (MulAut.conj (cs.simple i))).count t =
      l.count (cs.simple i * t * cs.simple i) := by
  have h := List.count_map_of_injective l (MulAut.conj (cs.simple i))
    (MulAut.conj (cs.simple i)).injective (cs.simple i * t * cs.simple i)
  simpa [MulAut.conj_apply, mul_assoc] using h

theorem signedWord_apply (ω : List B) (f : W → ZMod 2) (t : W) :
    signedWord cs ω f t =
      f ((cs.wordProd ω)⁻¹ * t * cs.wordProd ω) +
        ((cs.leftInvSeq ω).count t : ZMod 2) := by
  induction ω generalizing t with
  | nil =>
    change f t = _
    simp
  | cons i ω ih =>
    change signedWord cs ω f (cs.simple i * t * cs.simple i) +
        (if t = cs.simple i then 1 else 0) = _
    rw [ih]
    simp only [CoxeterSystem.wordProd_cons, mul_inv_rev, CoxeterSystem.inv_simple,
      CoxeterSystem.leftInvSeq, List.count_cons, count_conj]
    by_cases h : t = cs.simple i
    · simp [h, mul_assoc, add_assoc]
    · simp [h, Ne.symm h, mul_assoc]

private theorem alternating_inv_get (i j : B) (p k : ℕ) (hk : k < 2 * p) :
    (cs.leftInvSeq (CoxeterSystem.alternatingWord i j (2 * p)))[k]'(by simpa using hk) =
      cs.simple i * (cs.simple j * cs.simple i) ^ k := by
  rw [cs.getElem_leftInvSeq_alternatingWord i j p k hk,
    cs.prod_alternatingWord_eq_mul_pow]
  have ho : ¬Even (2 * k + 1) := Nat.not_even_iff_odd.mpr ⟨k, by omega⟩
  have hd : (2 * k + 1) / 2 = k := by omega
  simp [ho, hd]

/-- Each defining relation contributes its inversion list twice. -/
private theorem alternating_inv_double (i j : B) :
    let l := cs.leftInvSeq (CoxeterSystem.alternatingWord i j (2 * M i j))
    l = l.take (M i j) ++ l.take (M i j) := by
  dsimp
  let l := cs.leftInvSeq (CoxeterSystem.alternatingWord i j (2 * M i j))
  have hl : l.length = 2 * M i j := by simp [l]
  have he : l.drop (M i j) = l.take (M i j) := by
    apply List.ext_getElem
    · simp [hl]; omega
    · intro k hk hk'
      simp only [List.getElem_drop, List.getElem_take]
      have hk0 : k < M i j := by
        rw [List.length_drop, hl] at hk
        omega
      change l[M i j + k]'_ = l[k]'_
      dsimp [l]
      rw [alternating_inv_get cs i j (M i j) (M i j + k) (by omega),
        alternating_inv_get cs i j (M i j) k (by omega), pow_add,
        cs.simple_mul_simple_pow']
      simp
  calc
    _ = l.take (M i j) ++ l.drop (M i j) := (List.take_append_drop _ l).symm
    _ = _ := by rw [he]

private theorem signedWord_even (i j : B) (p : ℕ) :
    signedWord cs (CoxeterSystem.alternatingWord i j (2 * p)) =
      (signedSimple cs i * signedSimple cs j) ^ p := by
  induction p with
  | zero => rfl
  | succ p ih =>
    have he : Even (2 * p) := ⟨p, by omega⟩
    have ho : ¬Even (2 * p + 1) := Nat.not_even_iff_odd.mpr ⟨p, by omega⟩
    rw [show 2 * (p + 1) = (2 * p + 1) + 1 by omega,
      CoxeterSystem.alternatingWord_succ', CoxeterSystem.alternatingWord_succ']
    simp only [ho, he, ite_false, ite_true]
    change signedSimple cs i * (signedSimple cs j *
      signedWord cs (CoxeterSystem.alternatingWord i j (2 * p))) = _
    rw [ih, pow_succ', mul_assoc]

private theorem signedSimple_relations : CoxeterMatrix.IsLiftable M (signedSimple cs) := by
  intro i j
  rw [← signedWord_even cs i j]
  funext f t
  rw [signedWord_apply]
  have hp : cs.wordProd (CoxeterSystem.alternatingWord i j (2 * M i j)) = 1 := by
    rw [cs.prod_alternatingWord_eq_mul_pow]
    simp
  rw [hp, alternating_inv_double cs i j, List.count_append, Nat.cast_add]
  change f (1⁻¹ * t * 1) + _ = f t
  simp [← two_mul, show (2 : ZMod 2) = 0 by decide]

def signedAction : W →* Function.End (W → ZMod 2) :=
  cs.lift ⟨signedSimple cs, signedSimple_relations cs⟩

theorem signedAction_word (ω : List B) :
    signedAction cs (cs.wordProd ω) = signedWord cs ω := by
  induction ω with
  | nil => exact map_one _
  | cons i ω ih =>
    rw [CoxeterSystem.wordProd_cons, map_mul, ih]
    change cs.lift ⟨signedSimple cs, signedSimple_relations cs⟩ (cs.simple i) * _ = _
    rw [CoxeterSystem.lift_apply_simple]
    rfl

/-- The parity of each inversion count depends only on the group element. -/
private theorem invCount_eq_of_prod_eq {ω η : List B}
    (h : cs.wordProd ω = cs.wordProd η) (t : W) :
    ((cs.leftInvSeq ω).count t : ZMod 2) = ((cs.leftInvSeq η).count t : ZMod 2) := by
  have he := congrArg (fun g : Function.End (W → ZMod 2) => g (fun _ => 0) t)
    (congrArg (signedAction cs) h)
  simpa only [signedAction_word, signedWord_apply, zero_add] using he

/-- A simple left descent occurs in every word's left inversion sequence. -/
theorem simple_mem_leftInvSeq_of_descent {ω : List B} {i : B}
    (hi : cs.length (cs.simple i * cs.wordProd ω) < cs.length (cs.wordProd ω)) :
    cs.simple i ∈ cs.leftInvSeq ω := by
  obtain ⟨η, hη, hp⟩ := cs.exists_isReduced (cs.simple i * cs.wordProd ω)
  have he : cs.wordProd (i :: η) = cs.wordProd ω := by
    rw [CoxeterSystem.wordProd_cons, ← hp, CoxeterSystem.simple_mul_simple_cancel_left]
  have hr : cs.IsReduced (i :: η) := by
    rw [CoxeterSystem.IsReduced, he, List.length_cons, ← hη.eq, ← hp]
    exact (cs.isLeftDescent_iff.mp hi).symm
  have hc : (cs.leftInvSeq (i :: η)).count (cs.simple i) = 1 :=
    List.count_eq_one_of_mem hr.nodup_leftInvSeq (by simp [CoxeterSystem.leftInvSeq])
  have hcount := invCount_eq_of_prod_eq cs he (cs.simple i)
  rw [hc, Nat.cast_one] at hcount
  by_contra hn
  rw [List.count_eq_zero_of_not_mem hn, Nat.cast_zero] at hcount
  exact one_ne_zero hcount

/-- The simple exchange condition, valid even for an unreduced input word. -/
theorem simple_left_exchange {ω : List B} {i : B}
    (hi : cs.length (cs.simple i * cs.wordProd ω) < cs.length (cs.wordProd ω)) :
    ∃ k < ω.length,
      cs.simple i * cs.wordProd ω = cs.wordProd (ω.eraseIdx k) := by
  obtain ⟨k, hk, he⟩ := List.mem_iff_getElem.mp
    (simple_mem_leftInvSeq_of_descent cs hi)
  refine ⟨k, by simpa using hk, ?_⟩
  rw [← he, ← List.getD_eq_getElem _ 1 hk]
  exact cs.getD_leftInvSeq_mul_wordProd ω k

/-- Exchange split at a concatenation: the deleted letter is in one of the two words. -/
theorem simple_left_exchange_append {α β : List B} {i : B}
    (hi : cs.length (cs.simple i * cs.wordProd (α ++ β)) <
      cs.length (cs.wordProd (α ++ β))) :
    (∃ k < α.length,
      cs.simple i * cs.wordProd (α ++ β) = cs.wordProd (α.eraseIdx k ++ β)) ∨
    (∃ k < β.length,
      cs.simple i * cs.wordProd (α ++ β) = cs.wordProd (α ++ β.eraseIdx k)) := by
  obtain ⟨k, hk, he⟩ := simple_left_exchange cs hi
  by_cases hka : k < α.length
  · left
    refine ⟨k, hka, ?_⟩
    simpa [List.eraseIdx_append_of_lt_length hka] using he
  · right
    refine ⟨k - α.length, by simpa using (show k - α.length < β.length by
      rw [List.length_append] at hk; omega), ?_⟩
    simpa [List.eraseIdx_append_of_length_le (Nat.le_of_not_gt hka)] using he

end
end Langlands.Group.RelativeWeylIndexing
