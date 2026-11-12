import Langlands.AbelianScheme.FieldCubePullbackStatement
import Langlands.AbelianScheme.FieldCubePullbackAssembly
import Langlands.AlgebraicGeometry.Picard.FieldCubeIsomorphismProof

/-! # The balanced cube pullback identity over arbitrary fields -/

universe u

namespace Langlands.GroupScheme

/-- The balanced cube identity for actual line-bundle pullbacks along three
maps from an arbitrary scheme to an abelian variety over any field. -/
theorem fieldCubePullback : FieldCubePullbackStatement.{u} :=
  fieldCubePullbackOfIsomorphism
    Langlands.AlgebraicGeometry.Picard.fieldCubeIsomorphism.{u}

end Langlands.GroupScheme
