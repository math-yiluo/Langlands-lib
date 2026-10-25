import Langlands.Representation.Jacquet.RefinedOppositeStableImageProof

namespace Langlands.Jacquet

universe uF uV

/-- The closed product-Levi opposite canonical-lift family. -/
theorem refinedOppositeCanonicalLift : RefinedOppositeCanonicalLiftStatement.{uF,uV} := by
  intro p _ F T n B S V _ _
  exact ⟨refinedOppositePowerKernelJacquet F T B S V,
    refinedOppositeStableImageJacquetBijective F T B S V⟩

end Langlands.Jacquet
