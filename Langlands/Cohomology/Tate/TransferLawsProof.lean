import Langlands.Cohomology.Tate.TransferStatement
import Langlands.Cohomology.Tate.SplitTransfer

universe u

namespace Langlands.Tate

/-- The constructed subgroup maps satisfy the exact transfer-law proposition. -/
theorem transferLaws : TransferLaws.{u} := by
  intro R G _ _ _ H _ _
  refine ⟨?_, ?_, ?_⟩
  · intro A B f n
    exact ⟨restriction_naturality H n f, corestriction_naturality H n f⟩
  · exact corestriction_restriction H
  · intro S hS hs n
    obtain ⟨s⟩ := hs
    exact ⟨restriction_scalarSplit_delta H S s n, corestriction_scalarSplit_delta H S s n⟩

-- Check the complete unapplied theorem in the arbitrary carrier universe.
example : TransferLaws.{u} := @transferLaws.{u}

end Langlands.Tate
