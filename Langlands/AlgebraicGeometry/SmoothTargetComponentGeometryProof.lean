import Langlands.AlgebraicGeometry.SmoothTargetComponentGeometryStatement
import Langlands.AlgebraicGeometry.SmoothPureDimensionProof

/-! # Pure fibre geometry on actual target-component restrictions -/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Langlands.AlgebraicGeometry

/-- Each selected target-component chart dimension gives the full actual
residue-fibre property, and the restrictions retain their structure maps. -/
theorem smoothTargetComponentGeometry : SmoothTargetComponentGeometryStatement.{u} := by
  constructor
  · intro X Y _ f _ _ c
    apply SchemeFiberGeometry.nonemptyGeometricallyConnectedPureDimensionFibers_iff
      (targetComponentRestriction f c) |>.mpr
    exact ⟨inferInstance, smoothPureDimension.2 _ _ _
      (smoothTargetComponentDimensions f c) (smoothTargetComponentDimensions_spec f c)⟩
  · intro B X Y _ _ p q _ _ _ _ _ _ f c
    exact ⟨inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, inferInstance⟩

end Langlands.AlgebraicGeometry
