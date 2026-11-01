import Langlands.Representation.Classification.IntegralCuspidalJacquetWordOrderedRunsStatement
import Langlands.Representation.Classification.IntegralCuspidalJacquetWordLocalMovesProof
import Langlands.Combinatorics.PermutationLexMinimumProof
import Langlands.Combinatorics.LexMinimalConsecutiveRunsProof

/-! # Ordered runs of a least realized cuspidal Jacquet word -/

namespace Langlands.Classification

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (T : F.TopologicalData)

private theorem swap_pair_perm (l r : List ℤ) (a b : ℤ) :
    (l ++ [b, a] ++ r).Perm (l ++ [a, b] ++ r) := by
  simpa only [List.append_assoc] using
    ((List.Perm.swap a b []).append_left l).append_right r

private theorem lower_repeat_perm (l r : List ℤ) (b : ℤ) :
    (l ++ [b, b + 1, b] ++ r).Perm (l ++ [b + 1, b, b] ++ r) := by
  simpa only [List.append_assoc] using
    ((List.Perm.swap (b + 1) b [b]).append_left l).append_right r

private theorem upper_repeat_left_perm (l r : List ℤ) (b : ℤ) :
    (l ++ [b + 1, b + 1, b] ++ r).Perm (l ++ [b + 1, b, b + 1] ++ r) := by
  simpa only [List.append_assoc] using
    (((List.Perm.swap b (b + 1) []).cons (b + 1)).append_left l).append_right r

private theorem upper_repeat_right_perm (l r : List ℤ) (b : ℤ) :
    (l ++ [b, b + 1, b + 1] ++ r).Perm (l ++ [b + 1, b, b + 1] ++ r) := by
  simpa only [List.append_assoc] using
    ((List.Perm.swap (b + 1) b [b + 1]).append_left l).append_right r

theorem integralCuspidalJacquetWordOrderedRuns :
    IntegralCuspidalJacquetWordOrderedRuns.{uF,uV} F T := by
  intro hinterchange hirreducible htransfer
  let := T.topology
  intro m n A π hπ hAdm hFL w₀ h₀
  let P := IntegralCuspidalJacquetWord F T m n A π
  obtain ⟨w, hw, hperm, hmin⟩ :=
    Combinatorics.permutationLexMinimum P w₀ h₀
  obtain ⟨swap, abb, aba⟩ :=
    integralCuspidalJacquetWordLocalMoves F T hinterchange hirreducible htransfer
      m n A π hπ hAdm hFL
  let Q : List ℤ → Prop := fun v => P v ∧ v.Perm w₀
  have qswap : ∀ (l r : List ℤ) (a b : ℤ), a + 1 ≠ b → b + 1 ≠ a →
      Q (l ++ [a, b] ++ r) → Q (l ++ [b, a] ++ r) := by
    intro l r a b hab hba hv
    exact ⟨swap l r a b hab hba hv.1, (swap_pair_perm l r a b).trans hv.2⟩
  have qabb : ∀ (l r : List ℤ) (b : ℤ),
      Q (l ++ [b + 1, b, b] ++ r) → Q (l ++ [b, b + 1, b] ++ r) := by
    intro l r b hv
    exact ⟨abb l r b hv.1, (lower_repeat_perm l r b).trans hv.2⟩
  have qaba : ∀ (l r : List ℤ) (b : ℤ),
      Q (l ++ [b + 1, b, b + 1] ++ r) →
        Q (l ++ [b + 1, b + 1, b] ++ r) ∨
        Q (l ++ [b, b + 1, b + 1] ++ r) := by
    intro l r b hv
    rcases aba l r b hv.1 with hleft | hright
    · exact Or.inl ⟨hleft, (upper_repeat_left_perm l r b).trans hv.2⟩
    · exact Or.inr ⟨hright, (upper_repeat_right_perm l r b).trans hv.2⟩
  have hQmin : ∀ v, Q v → ¬ List.Lex (· < ·) v w := by
    intro v hv
    exact hmin v hv.1 hv.2
  exact ⟨w, hw, hperm, hmin,
    Combinatorics.lexMinimalConsecutiveRuns Q qswap qabb qaba w ⟨hw, hperm⟩ hQmin⟩

end Langlands.Classification
