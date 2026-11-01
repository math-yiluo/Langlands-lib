import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Lex
import Mathlib.Data.List.Range

/-! # Consecutive runs in a lexicographically minimal integer word -/

namespace Langlands.Combinatorics

/-- A lexicographically minimal word in a family closed under the unlinked
adjacent swap and the two repeated-factor triple moves is a concatenation of
nonempty descending consecutive runs with nondecreasing first entries. -/
def LexMinimalConsecutiveRuns : Prop :=
  ∀ (P : List ℤ → Prop),
    (∀ (l r : List ℤ) (a b : ℤ),
      a + 1 ≠ b → b + 1 ≠ a →
      P (l ++ [a, b] ++ r) → P (l ++ [b, a] ++ r)) →
    (∀ (l r : List ℤ) (b : ℤ),
      P (l ++ [b + 1, b, b] ++ r) →
        P (l ++ [b, b + 1, b] ++ r)) →
    (∀ (l r : List ℤ) (b : ℤ),
      P (l ++ [b + 1, b, b + 1] ++ r) →
        P (l ++ [b + 1, b + 1, b] ++ r) ∨
        P (l ++ [b, b + 1, b + 1] ++ r)) →
    ∀ (w : List ℤ), P w →
      (∀ v, P v → ¬ List.Lex (· < ·) v w) →
      ∃ runs : List (ℤ × ℕ),
        (∀ s ∈ runs, 0 < s.2) ∧
        runs.IsChain (fun s t => s.1 ≤ t.1) ∧
        w = runs.flatMap (fun s =>
          (List.range s.2).map (fun j => s.1 - (j : ℤ)))

end Langlands.Combinatorics
