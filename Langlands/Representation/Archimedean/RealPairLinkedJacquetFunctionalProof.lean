import Langlands.Representation.Archimedean.RealInterlacedMirror

/-!
# Two linked blocks: proof of `RealPairLinkedJacquetFunctionalStatement`

The four kinds of pairs of `RealLinkedJacquetPairReduction`:

* two characters (CC), from the character case `realCharacterLinkedJacquetFunctional` of
  `RealCharacterCrossing` applied to the list `[c, d]`;
* an induction block and a character (IC) and a character and an induction block (CI), from
  `RealBlockFlatJacquet`;
* two induction blocks (II), from `RealBlockFlatJacquet` (separated case) and
  `RealInterlacedMirror` (interlaced case).

`realPairLinkedJacquetFunctional_of_kinds` combines them.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean
open RealStrictCharacterLanglandsQuotient (IsCharacterList)

/-- **CC**: two linked characters `c`, `d` with `Re t(d) ≤ Re t(c)`, from the character case of
`RealLinkedJacquetFunctionalStatement` for the list `[c, d]`. -/
theorem realCharacterPairLinkedJacquetFunctional :
    RealCharacterPairLinkedJacquetFunctionalStatement := by
  intro c d hexp hun
  have hchar : IsCharacterList [RealBlock.character c, RealBlock.character d] := by
    intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact ⟨c, rfl⟩
    · exact ⟨d, rfl⟩
  have hord : IsRealLanglandsOrdered [RealBlock.character c, RealBlock.character d] := by
    simp [IsRealLanglandsOrdered, hexp]
  have hlink : ¬ IsRealMoeglinUnlinked [RealBlock.character c, RealBlock.character d] := by
    intro h
    apply hun
    intro a ha b hb
    simp only [realBlockMoeglinData, List.mem_singleton] at ha hb
    subst ha hb
    simp only [IsRealMoeglinUnlinked, realMoeglinData, List.flatMap_cons, List.flatMap_nil,
      realBlockMoeglinData, List.singleton_append, List.append_nil, List.pairwise_cons,
      List.mem_singleton, forall_eq, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
      List.Pairwise.nil, and_true] at h
    exact h
  exact realCharacterLinkedJacquetFunctional 2 _ rfl hchar hord hlink

/-- **Two linked blocks.** For nondegenerate real blocks `x`, `z` with `Re t(z) ≤ Re t(x)` and a
linked pair of Mœglin data, the standard module of `[x, z]` carries a functional as in
`RealLinkedJacquetFunctionalExists`. -/
theorem realPairLinkedJacquetFunctional : RealPairLinkedJacquetFunctionalStatement :=
  realPairLinkedJacquetFunctional_of_kinds realCharacterPairLinkedJacquetFunctional
    RealBlockFlatJacquet.realInducedCharacterLinkedJacquetFunctional
    RealBlockFlatJacquet.realCharacterInducedLinkedJacquetFunctional
    realInducedInducedLinkedJacquetFunctional

end Langlands.Archimedean
