import Mathlib.Data.List.Lex
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.Pairwise

/-! A least concatenation of permutations of decreasing blocks fixes each block. -/

namespace Langlands.Combinatorics

universe u

variable {α : Type u} [LinearOrder α]

theorem eq_or_lex_of_perm_decreasing {s v : List α}
    (hs : s.Pairwise (· ≥ ·)) (hp : v.Perm s) :
    v = s ∨ List.Lex (· < ·) v s := by
  induction s generalizing v with
  | nil =>
      exact Or.inl (List.perm_nil.mp hp)
  | cons a s ih =>
      cases v with
      | nil => simp at hp
      | cons b v =>
          obtain ⟨ha, hspair⟩ := List.pairwise_cons.mp hs
          have hba : b ≤ a := by
            have hb : b ∈ a :: s := hp.mem_iff.mp (List.mem_cons_self ..)
            rcases List.mem_cons.mp hb with h | h
            · exact le_of_eq h
            · exact ha b h
          rcases lt_or_eq_of_le hba with h | heq
          · exact Or.inr (List.Lex.rel h)
          · subst b
            rcases ih hspair (List.Perm.cons_inv hp) with h | h
            · exact Or.inl (congrArg (List.cons a) h)
            · exact Or.inr (List.Lex.cons h)

theorem lex_append_of_length_eq {s v : List α}
    (h : List.Lex (· < ·) v s) (hlen : v.length = s.length)
    (v' s' : List α) :
    List.Lex (· < ·) (v ++ v') (s ++ s') := by
  induction h with
  | nil => simp at hlen
  | rel h => exact List.Lex.rel h
  | cons h ih =>
      exact List.Lex.cons (ih (Nat.succ.inj hlen))

theorem eq_blocks_of_minimal_flatten {vs ss : List (List α)}
    (hp : List.Forall₂ List.Perm vs ss)
    (hs : ∀ s ∈ ss, s.Pairwise (· ≥ ·))
    (hmin : ¬ List.Lex (· < ·) vs.flatten ss.flatten) :
    vs = ss := by
  induction hp with
  | nil => rfl
  | @cons v s vs ss hp hps ih =>
      have hsorted := hs s (List.mem_cons_self ..)
      rcases eq_or_lex_of_perm_decreasing hsorted hp with h | h
      · subst v
        have hmin' : ¬ List.Lex (· < ·) vs.flatten ss.flatten := by
          intro h
          exact hmin (by
            simpa only [List.flatten_cons] using
              h.append_left (· < ·) s)
        have htail := ih (fun t ht => hs t (List.mem_cons_of_mem s ht)) hmin'
        exact congrArg (List.cons s) htail
      · exact False.elim (hmin (by
          simpa only [List.flatten_cons] using
            lex_append_of_length_eq h hp.length_eq vs.flatten ss.flatten))

end Langlands.Combinatorics
