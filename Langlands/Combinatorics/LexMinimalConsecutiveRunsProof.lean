import Langlands.Combinatorics.LexMinimalConsecutiveRunsStatement
import Mathlib.Tactic

/-! # Finite-word proof of the ordered consecutive-run decomposition -/

namespace Langlands.Combinatorics

private def run (a : ℤ) : ℕ → List ℤ
  | 0 => []
  | m + 1 => a :: run (a - 1) m

private theorem run_length (a : ℤ) (m : ℕ) : (run a m).length = m := by
  induction m generalizing a with
  | zero => rfl
  | succ m ih => simp [run, ih]

private theorem run_range (a : ℤ) (m : ℕ) :
    run a m = (List.range m).map (fun j : ℕ => a - (j : ℤ)) := by
  induction m generalizing a with
  | zero => rfl
  | succ m ih =>
    simp only [run, List.range_succ_eq_map, List.map_cons, List.map_map,
      Int.natCast_zero, sub_zero]
    congr 1
    rw [ih]
    apply List.map_congr_left
    intro j _
    simp only [Function.comp_apply, Int.natCast_succ]
    omega

private theorem run_add (a : ℤ) (m n : ℕ) :
    run a (m + n) = run a m ++ run (a - (m : ℤ)) n := by
  induction m generalizing a with
  | zero => simp [run]
  | succ m ih =>
    rw [Nat.succ_add, run, run, List.cons_append, ih]
    rw [show a - 1 - (m : ℤ) = a - ((m + 1 : ℕ) : ℤ) by omega]

private theorem run_last (a : ℤ) (m : ℕ) :
    run a (m + 1) = run a m ++ [a - (m : ℤ)] := by
  simpa [run] using run_add a m 1

private theorem run_bound (a : ℤ) (m : ℕ) (y : ℤ) (hy : y ∈ run a m) :
    a - (m : ℤ) < y ∧ y ≤ a := by
  rw [run_range] at hy
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hy
  have hj' := List.mem_range.mp hj
  omega

private theorem run_prefix (a : ℤ) (w : List ℤ) :
    ∃ (m : ℕ), 0 < m ∧ ∃ r : List ℤ,
      a :: w = run a m ++ r ∧
      (∀ x ∈ r.head?, x ≠ a - (m : ℤ)) := by
  induction w generalizing a with
  | nil => exact ⟨1, by omega, [], by simp [run]⟩
  | cons b w ih =>
    by_cases hba : b = a - 1
    · obtain ⟨m, hm, r, heq, hend⟩ := ih b
      refine ⟨m + 1, by omega, r, ?_, ?_⟩
      · simpa only [run, List.cons_append, ← hba] using congrArg (List.cons a) heq
      · intro x hx he
        apply hend x hx
        omega
    · refine ⟨1, by omega, b :: w, by simp [run], ?_⟩
      intro x hx
      have hxb : x = b := by simpa only [List.head?_cons, Option.mem_def,
        Option.some.injEq, eq_comm] using hx
      simpa [hxb] using hba

section Moves

variable (P : List ℤ → Prop)
variable
  (swap : ∀ (l r : List ℤ) (a b : ℤ),
    a + 1 ≠ b → b + 1 ≠ a →
    P (l ++ [a, b] ++ r) → P (l ++ [b, a] ++ r))
  (abb : ∀ (l r : List ℤ) (b : ℤ),
    P (l ++ [b + 1, b, b] ++ r) → P (l ++ [b, b + 1, b] ++ r))
  (aba : ∀ (l r : List ℤ) (b : ℤ),
    P (l ++ [b + 1, b, b + 1] ++ r) →
      P (l ++ [b + 1, b + 1, b] ++ r) ∨
      P (l ++ [b, b + 1, b + 1] ++ r))

include swap in
private theorem commute_left (l r t : List ℤ) (x : ℤ)
    (ht : ∀ y ∈ t, y + 1 < x)
    (h : P (l ++ t ++ x :: r)) :
    P (l ++ x :: (t ++ r)) := by
  induction t generalizing l with
  | nil => simpa using h
  | cons y t ih =>
    have ht' : ∀ z ∈ t, z + 1 < x := fun z hz => ht z (by simp [hz])
    have h' : P ((l ++ [y]) ++ x :: (t ++ r)) :=
      ih (l ++ [y]) ht' (by simpa [List.append_assoc] using h)
    have hy := ht y (by simp)
    simpa [List.append_assoc] using
      swap l (t ++ r) y x (by omega) (by omega)
        (by simpa [List.append_assoc] using h')

include swap abb aba in
private theorem interior_repeat (l r t : List ℤ) (x : ℤ)
    (ht : ∀ y ∈ t, y + 1 < x)
    (h : P (l ++ [x + 1, x, x - 1] ++ t ++ x :: r)) :
    ∃ v, P v ∧ List.Lex (· < ·) v
      (l ++ [x + 1, x, x - 1] ++ t ++ x :: r) := by
  have h' : P ((l ++ [x + 1, x, x - 1]) ++ x :: (t ++ r)) :=
    commute_left P swap _ _ _ _ ht (by simpa [List.append_assoc] using h)
  have h'' : P ((l ++ [x + 1]) ++ [x, x - 1, x] ++ (t ++ r)) := by
    simpa [List.append_assoc] using h'
  have hx : x - 1 + 1 = x := by omega
  rcases aba (l ++ [x + 1]) (t ++ r) (x - 1) (by simpa [hx] using h'') with hA | hB
  · have hA' : P (l ++ [x + 1, x, x] ++ ((x - 1) :: (t ++ r))) := by
      simpa [hx, List.append_assoc] using hA
    have hlow := abb l ((x - 1) :: (t ++ r)) x hA'
    refine ⟨_, hlow, ?_⟩
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    apply List.Lex.append_left
    exact List.Lex.rel (by omega)
  · refine ⟨_, hB, ?_⟩
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    apply List.Lex.append_left
    apply List.Lex.cons
    exact List.Lex.rel (by omega)

include swap abb aba in
private theorem run_next (l r : List ℤ) (a x : ℤ) (m : ℕ) (hm : 0 < m)
    (hx : x < a) (h : P (l ++ run a m ++ x :: r))
    (hmin : ∀ v, P v → ¬ List.Lex (· < ·) v (l ++ run a m ++ x :: r)) :
    x = a - (m : ℤ) := by
  by_contra hne
  cases m with
  | zero => omega
  | succ n =>
    let c : ℤ := a - (n : ℤ)
    have hc : c = a - (n : ℤ) := rfl
    rcases lt_trichotomy x c with hxc | hxc | hcx
    · have hgap : x + 1 < c := by omega
      have h' : P ((l ++ run a n) ++ [c, x] ++ r) := by
        simpa [run_last, hc, List.append_assoc] using h
      have hlow := swap (l ++ run a n) r c x (by omega) (by omega) h'
      apply hmin _ hlow
      simp only [run_last, ← hc, List.append_assoc, List.cons_append, List.nil_append]
      apply List.Lex.append_left
      apply List.Lex.append_left
      exact List.Lex.rel (by omega)
    · subst x
      cases n with
      | zero => simp [c] at hx
      | succ k =>
        have heq : run a (k + 1 + 1) =
            run a k ++ [c + 1, c] := by
          rw [show k + 1 + 1 = k + 2 by omega, run_add,
            show a - (k : ℤ) = c + 1 by omega]
          simp only [run, show c + 1 - 1 = c by omega]
        have h' : P ((l ++ run a k) ++ [c + 1, c, c] ++ r) := by
          simpa [heq, List.append_assoc] using h
        have hlow := abb (l ++ run a k) r c h'
        apply hmin _ hlow
        simp only [heq, List.append_assoc, List.cons_append, List.nil_append]
        apply List.Lex.append_left
        apply List.Lex.append_left
        exact List.Lex.rel (by omega)
    · let k : ℕ := (a - x - 1).toNat
      have hk : (k : ℤ) = a - x - 1 := Int.toNat_of_nonneg (by omega)
      have hkm : k + 3 ≤ n + 1 := by omega
      let t : List ℤ := run (x - 2) (n + 1 - k - 3)
      have heq : run a (n + 1) = run a k ++ [x + 1, x, x - 1] ++ t := by
        rw [show n + 1 = k + (3 + (n + 1 - k - 3)) by omega, run_add,
          show a - (k : ℤ) = x + 1 by omega, run_add]
        simp only [run, List.append_assoc]
        dsimp [t]
        rw [show x + 1 - 1 = x by omega, show x + 1 - 3 = x - 2 by omega]
      have ht : ∀ y ∈ t, y + 1 < x := by
        intro y hy
        have hb := (run_bound (x - 2) (n + 1 - k - 3) y hy).2
        omega
      obtain ⟨v, hv, hlex⟩ := interior_repeat P swap abb aba (l ++ run a k) r t x ht
        (by simpa [heq, List.append_assoc] using h)
      exact hmin v hv (by simpa [heq, List.append_assoc] using hlex)

end Moves

theorem lexMinimalConsecutiveRuns : LexMinimalConsecutiveRuns := by
  intro P swap abb aba w hw hmin
  suffices H : ∃ runs : List (ℤ × ℕ),
      (∀ s ∈ runs, 0 < s.2) ∧
      runs.IsChain (fun s t => s.1 ≤ t.1) ∧
      w = runs.flatMap (fun s => run s.1 s.2) by
    simpa [run_range, ← List.map_eq_flatMap, List.map_map, Function.comp_def] using H
  generalize hn : w.length = n
  induction n using Nat.strong_induction_on generalizing P w with
  | h n ih =>
    cases w with
    | nil => exact ⟨[], by simp⟩
    | cons a w =>
      obtain ⟨m, hm, r, heq, hend⟩ := run_prefix a w
      have hhead : ∀ x ∈ r.head?, a ≤ x := by
        intro x hx
        by_contra hax
        have hword : [] ++ run a m ++ x :: r.tail = a :: w := by
          simpa only [List.nil_append, List.cons_head?_tail hx] using heq.symm
        have he := run_next P swap abb aba [] r.tail a x m hm (by omega)
          (by simpa only [hword] using hw) (by simpa only [hword] using hmin)
        exact hend x hx he
      let Q : List ℤ → Prop := fun v => P (run a m ++ v)
      have qswap : ∀ (l t : List ℤ) (x y : ℤ),
          x + 1 ≠ y → y + 1 ≠ x →
          Q (l ++ [x, y] ++ t) → Q (l ++ [y, x] ++ t) := by
        intro l t x y hxy hyx hp
        simpa only [Q, List.append_assoc] using
          (swap (run a m ++ l) t x y hxy hyx
            (by simpa only [Q, List.append_assoc] using hp))
      have qabb : ∀ (l t : List ℤ) (b : ℤ),
          Q (l ++ [b + 1, b, b] ++ t) → Q (l ++ [b, b + 1, b] ++ t) := by
        intro l t b hp
        simpa only [Q, List.append_assoc] using
          (abb (run a m ++ l) t b (by simpa only [Q, List.append_assoc] using hp))
      have qaba : ∀ (l t : List ℤ) (b : ℤ),
          Q (l ++ [b + 1, b, b + 1] ++ t) →
            Q (l ++ [b + 1, b + 1, b] ++ t) ∨
            Q (l ++ [b, b + 1, b + 1] ++ t) := by
        intro l t b hp
        simpa only [Q, List.append_assoc] using
          (aba (run a m ++ l) t b (by simpa only [Q, List.append_assoc] using hp))
      have qh : Q r := by simpa only [Q, ← heq] using hw
      have qmin : ∀ v, Q v → ¬ List.Lex (· < ·) v r := by
        intro v hv hlex
        apply hmin (run a m ++ v) hv
        rw [heq]
        exact List.Lex.append_left _ hlex _
      have hlen : r.length < n := by
        have hl := congrArg List.length heq
        simp only [List.length_cons, List.length_append, run_length] at hl
        simp only [List.length_cons] at hn
        omega
      obtain ⟨runs, hpos, hchain, hflat⟩ :=
        ih r.length hlen Q qswap qabb qaba r qh qmin rfl
      refine ⟨(a, m) :: runs, ?_, ?_, ?_⟩
      · simpa only [List.mem_cons, forall_eq_or_imp] using And.intro hm hpos
      · cases runs with
        | nil => simp
        | cons s ss =>
          have hs : 0 < s.2 := hpos s (by simp)
          have hshead : s.1 ∈ r.head? := by
            rw [hflat, List.flatMap_cons]
            cases hs2 : s.2 with
            | zero => omega
            | succ k => simp [run]
          exact List.isChain_cons_cons.mpr ⟨hhead _ hshead, hchain⟩
      · simpa only [List.flatMap_cons] using heq.trans (congrArg (run a m ++ ·) hflat)

end Langlands.Combinatorics
