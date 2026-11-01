import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Lex
import Mathlib.Data.List.Permutation

/-! # A least word among the realized permutations of one word -/

namespace Langlands.Combinatorics

/-- A predicate satisfied by one integer word has a lexicographically least
word among the permutations of that word which satisfy the predicate. -/
def PermutationLexMinimum : Prop :=
  ∀ (P : List ℤ → Prop) (w₀ : List ℤ), P w₀ →
    ∃ w : List ℤ, P w ∧ w.Perm w₀ ∧
      ∀ v : List ℤ, P v → v.Perm w₀ → ¬ List.Lex (· < ·) v w

end Langlands.Combinatorics
