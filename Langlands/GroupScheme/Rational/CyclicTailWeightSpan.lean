import Langlands.GroupScheme.Rational.WeightSemigroupStatement

/-! # Reindexing the weight span of a positive cyclic tail -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-- The span selected by a cyclic tail is indexed by its positive integer
multipliers; repeated characters do not affect the supremum. -/
theorem semigroupWeightSpan_cyclicTail (b : AutomorphicAction S.toGrp G)
    (a : characterLattice S) (j : ℕ) :
    semigroupWeightSpan b (cyclicTail a j) =
      ⨆ n : {n : ℕ // j ≤ n ∧ 0 < n}, actionWeightSpace b (n.val • a) := by
  apply le_antisymm
  · apply iSup_le
    intro χ
    obtain ⟨n, hn, hn0, he⟩ := χ.property
    rw [← he]
    exact le_iSup (fun m : {n : ℕ // j ≤ n ∧ 0 < n} =>
      actionWeightSpace b (m.val • a)) ⟨n, hn, hn0⟩
  · apply iSup_le
    intro n
    exact le_iSup (fun χ : cyclicTail a j => actionWeightSpace b χ.val)
      ⟨n.val • a, n.val, n.property.1, n.property.2, rfl⟩

end Langlands.GroupScheme.RelativeRoot
