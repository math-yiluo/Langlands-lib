import Langlands.AlgebraicGeometry.SmoothTargetComponentRestrictions
import Langlands.AlgebraicGeometry.SchemePureDimensionFibers
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Full fibre geometry on actual target-component restrictions -/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Langlands.AlgebraicGeometry

/-- The selected chart dimension on each actual target component is the
pure dimension of its nonempty geometrically connected residue fibres. -/
def SmoothTargetComponentFiberGeometryStatement : Prop :=
  ∀ (X Y : Scheme.{u}) [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [Smooth f] [GeometricallyConnected f]
    (c : ConnectedComponents Y),
    SchemeFiberGeometry.NonemptyGeometricallyConnectedPureDimensionFibers
      (smoothTargetComponentDimensions f c) (targetComponentRestriction f c)

/-- The actual source and target restrictions retain finite type and
separatedness over the original base. -/
def TargetComponentFiniteTypeSeparatedStatement : Prop :=
  ∀ (B X Y : Scheme.{u}) [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (p : X ⟶ B) (q : Y ⟶ B)
    [LocallyOfFiniteType p] [QuasiCompact p] [IsSeparated p]
    [LocallyOfFiniteType q] [QuasiCompact q] [IsSeparated q]
    (f : X ⟶ Y) (c : ConnectedComponents Y),
    LocallyOfFiniteType (componentPreimageι f c ≫ p) ∧
    QuasiCompact (componentPreimageι f c ≫ p) ∧
    IsSeparated (componentPreimageι f c ≫ p) ∧
    LocallyOfFiniteType (componentι Y c ≫ q) ∧
    QuasiCompact (componentι Y c ≫ q) ∧
    IsSeparated (componentι Y c ≫ q)

/-- The componentwise full fibre geometry and preservation of the actual
finite-type separated schemes used in Conrad's openness argument. -/
def SmoothTargetComponentGeometryStatement : Prop :=
  SmoothTargetComponentFiberGeometryStatement.{u} ∧
    TargetComponentFiniteTypeSeparatedStatement.{u}

end Langlands.AlgebraicGeometry
