import Langlands.Representation.Archimedean.RealInducedPairWeightZero
import Langlands.Representation.Archimedean.RealInductionStagesFiltration

/-!
# Removing weight-zero blocks from the two-induced-block filtration problem

The two `GL₃(ℝ)` filtration statements and induction in stages handle a pair of
induction blocks when either block has weight zero. Consequently the remaining
`GL₄(ℝ)` input can be restricted to two blocks of nonzero weight.

The `GL₃(ℝ)` statements are explicit hypotheses of this reduction.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean

attribute [local irreducible] RealAdjacentFiltration

/-- The two-induced-block filtration restricted to blocks of nonzero weight. -/
def RealInducedInducedNonzeroFiltrationStatement : Prop :=
  ∀ d e : ComplexCharacterData, d.weight ≠ 0 → e.weight ≠ 0 →
    realBlockExponent (.induced d) < realBlockExponent (.induced e) →
      RealAdjacentFiltration 4 [] [] (.induced d) (.induced e)

/-- The two `GL₃(ℝ)` base cases and the nonzero-weight `GL₄(ℝ)` case imply the full
two-induced-block filtration statement. -/
def RealInducedInducedFromNonzeroReductionStatement : Prop :=
  RealCharacterInducedFiltrationStatement → RealInducedCharacterFiltrationStatement →
    RealInducedInducedNonzeroFiltrationStatement → RealInducedInducedFiltrationStatement

namespace RealInducedInducedNonzeroReduction

open RealInducedPairWeightZero

/-- The character–induced `GL₃(ℝ)` statement handles a zero-weight left block,
with arbitrary surrounding lists. -/
theorem left_zero (hCI : RealCharacterInducedFiltrationStatement)
    (n : ℕ) (pre post : List RealBlock) (d e : ComplexCharacterData)
    (hd : d.weight = 0)
    (hrank : realRank (pre ++ .induced d :: .induced e :: post) = n)
    (hlt : realBlockExponent (.induced d) < realBlockExponent (.induced e)) :
    RealAdjacentFiltration n pre post (.induced d) (.induced e) := by
  apply fuse_left n pre post d (.induced e) hd
  · apply InductionStages.realAdjacentFiltrationInStages n
      (pre ++ [RealBlock.character (first d)]) post (.character (second d)) (.induced e)
    · simp only [realRank, List.map_append, List.map_cons, List.map_nil,
        List.sum_append, List.sum_cons, List.sum_nil, RealBlock.rank] at hrank ⊢
      omega
    · exact hCI (second d) e hlt
  · apply InductionStages.realAdjacentFiltrationInStages n pre
      (.character (second d) :: post) (.character (first d)) (.induced e)
    · simp only [realRank, List.map_append, List.map_cons,
        List.sum_append, List.sum_cons, RealBlock.rank] at hrank ⊢
      omega
    · exact hCI (first d) e hlt

/-- The induced–character `GL₃(ℝ)` statement handles a zero-weight right block,
with arbitrary surrounding lists. -/
theorem right_zero (hIC : RealInducedCharacterFiltrationStatement)
    (n : ℕ) (pre post : List RealBlock) (d e : ComplexCharacterData)
    (he : e.weight = 0)
    (hrank : realRank (pre ++ .induced d :: .induced e :: post) = n)
    (hlt : realBlockExponent (.induced d) < realBlockExponent (.induced e)) :
    RealAdjacentFiltration n pre post (.induced d) (.induced e) := by
  apply fuse_right n pre post (.induced d) e he
  · apply InductionStages.realAdjacentFiltrationInStages n pre
      (.character (second e) :: post) (.induced d) (.character (first e))
    · simp only [realRank, List.map_append, List.map_cons,
        List.sum_append, List.sum_cons, RealBlock.rank] at hrank ⊢
      omega
    · exact hIC d (first e) hlt
  · apply InductionStages.realAdjacentFiltrationInStages n
      (pre ++ [RealBlock.character (first e)]) post (.induced d) (.character (second e))
    · simp only [realRank, List.map_append, List.map_cons, List.map_nil,
        List.sum_append, List.sum_cons, List.sum_nil, RealBlock.rank] at hrank ⊢
      omega
    · exact hIC d (second e) hlt

end RealInducedInducedNonzeroReduction

/-- All weight-zero cases are discharged by the two `GL₃(ℝ)` inputs. -/
theorem realInducedInducedFromNonzeroReduction :
    RealInducedInducedFromNonzeroReductionStatement := by
  intro hCI hIC hII d e hlt
  by_cases hd : d.weight = 0
  · exact RealInducedInducedNonzeroReduction.left_zero hCI 4 [] [] d e hd
      (by simp [realRank, RealBlock.rank]) hlt
  by_cases he : e.weight = 0
  · exact RealInducedInducedNonzeroReduction.right_zero hIC 4 [] [] d e he
      (by simp [realRank, RealBlock.rank]) hlt
  exact hII d e hd he hlt

end Langlands.Archimedean
