import Langlands.Representation.Classification.AdjacentCuspidalJacquetInterchangeStatement
import Langlands.Representation.Parabolic.OrderedTensorOccurrences
import Langlands.Representation.CuspidalSupport.IrreducibleInductionOccurrence
import Langlands.Representation.CuspidalSupport.AdjacentInnerBinaryBridge

/-! Adjacent interchange of actual cuspidal Jacquet subquotients. -/

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.Classification

open GeneralLinear Parabolic CuspidalSupport

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- An irreducible commuting adjacent binary product permits interchange
inside an arbitrary actual cuspidal Jacquet occurrence. -/
theorem adjacentCuspidalJacquetInterchange :
    AdjacentCuspidalJacquetInterchange.{uF, uV} F T := by
  let := T.topology
  intro n B π hπi hπa hπfin A hA j hj a b hpair hiso
  have hn : 0 < n := lt_of_lt_of_le (by omega : 0 < B.length) B.length_le
  obtain ⟨X, hXi, hXa, hXfin, hX, hblocks⟩ :=
    exists_factorized_coarseJacquet_of_ordered F T B (B.adjacentMerge j hj)
      (B.adjacentRefinement j hj) (B.adjacentBlockEquiv j hj)
      (B.adjacentBlock_size j hj)
      (fun a b hab => (B.adjacentBlockEquiv_lt_iff j hj a b).mpr hab)
      hn π (fun i => (A i).obj) hπa hπfin
      (fun i => (A i).property.1) (fun i => (A i).property.2.1) hA
  have hinner : ∀ m, SmoothRep.IsSubquotient
      (adjacentInnerTensor F T B j hj A m)
      ((T.normalizedJacquetFunctor (B.adjacentRefinement j hj m)).obj (X m)) := by
    exact hblocks
  have hreverse : ∀ m, SmoothRep.IsSubquotient
      (adjacentReverseTensor F T B j hj A m)
      ((T.normalizedJacquetFunctor (B.adjacentReverseRefinement j hj m)).obj (X m)) := by
    intro m
    have hc := adjacentInnerTensors_cuspidal F T B j hj A m
    have hi := adjacentInnerInductions_irreducible_iso F T B j hj A hpair hiso m
    exact cuspidalOccurrence_transfer_of_inductionIso F T
      (B.adjacentRefinement j hj m) (B.adjacentReverseRefinement j hj m)
      (X m) (adjacentInnerTensor F T B j hj A m)
      (adjacentReverseTensor F T B j hj A m)
      (hXi m) (hXa m) hc.1.1 hc.1.2 hc.2.1 (hinner m) hi.1 hi.2
  apply subquotient_orderedJacquet_of_coarse_factors F T
    (B.permute (B.adjacentSwap j hj)) (B.adjacentMerge j hj)
    (B.adjacentReverseRefinement j hj) (B.adjacentBlockEquiv j hj)
    (B.adjacentReverse_size j hj)
    (fun a b hab => (B.adjacentBlockEquiv_lt_iff j hj a b).mpr hab)
    π X (fun i => (A (B.adjacentSwap j hj i)).obj) hX
  rw [adjacentReverseTensorFactors_eq F T B j hj A]
  exact hreverse

end Langlands.Classification
