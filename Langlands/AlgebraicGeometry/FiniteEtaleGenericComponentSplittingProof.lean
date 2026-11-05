import Langlands.AlgebraicGeometry.GenericComponentSplittingAssembly
import Langlands.AlgebraicGeometry.FiniteSeparableComponentSplittingProof
import Langlands.AlgebraicGeometry.FiniteSeparableGenericCoverProof

/-! # Finite étale splitting of actual generic-fibre components -/

universe u

namespace Langlands.AlgebraicGeometry.SchemeFiberGeometry

/-- Stacks 0551: an actual finite étale cover splits all actual generic-fibre
components geometrically. -/
theorem finiteTypeFiniteEtaleGenericComponentSplitting :
    FiniteTypeFiniteEtaleGenericComponentSplitting.{u} :=
  finiteTypeFiniteEtaleGenericComponentSplitting_of_fieldSplitting_and_cover
    finiteSeparableComponentSplitting finiteSeparableGenericCover

end Langlands.AlgebraicGeometry.SchemeFiberGeometry
