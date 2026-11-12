import Langlands.AlgebraicGeometry.Picard.RelativeRigidifiedCubeStatement
import Langlands.AlgebraicGeometry.Picard.FieldToRelativeCubeReduction
import Langlands.AlgebraicGeometry.Picard.FieldCubeTrivialityProof

/-! # Relative cube detection for actual rigidified families -/

universe u

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

/-- The ordinary relative three-face cube criterion over every quasi-separated base. -/
theorem relativeCubeTriviality : RelativeCubeTrivialityStatement.{u} :=
  relativeCubeTriviality_of_fieldCubeTriviality fieldCubeTriviality

/-- Two actual rigidified family classes over the parameter product of two abelian
schemes agree if their pullbacks along the two unit axes agree. -/
theorem relativeRigidifiedCube : RelativeRigidifiedCubeStatement.{u} :=
  relativeRigidifiedCube_of_relativeCubeTriviality relativeCubeTriviality

end Langlands.AbelianScheme
