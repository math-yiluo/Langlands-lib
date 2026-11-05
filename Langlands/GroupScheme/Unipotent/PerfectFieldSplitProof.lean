import Langlands.GroupScheme.Unipotent.PerfectFieldSplitStatement
import Langlands.GroupScheme.Unipotent.PerfectFieldSplitReduction
import Langlands.GroupScheme.Unipotent.OneDimensional.Proof
import Langlands.GroupScheme.UnipotentClosedSubgroupProof

/-! # Smooth connected unipotent groups over perfect fields are split -/

universe u

namespace Langlands.GroupScheme

/-- Every smooth connected affine unipotent group over a perfect field has a
finite represented split series with one-dimensional vector quotients. -/
theorem perfectFieldUnipotentSplit : PerfectFieldUnipotentSplitStatement.{u} := by
  intro k _ _ U _ _ hUc hUu
  exact Unipotent.perfectFieldSplit_of_oneDimensional
    unipotentClosedSubgroup perfectFieldOneDimensionalUnipotent k U hUc hUu

end Langlands.GroupScheme
