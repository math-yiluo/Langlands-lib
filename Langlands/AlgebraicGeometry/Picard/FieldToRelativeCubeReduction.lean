import Langlands.AlgebraicGeometry.Picard.RelativeCubeAssembly
import Langlands.AlgebraicGeometry.Picard.RelativeCubeTrivialityStatement
import Langlands.AlgebraicGeometry.Picard.LocalTwoAxisTrivialityProof
import Langlands.AlgebraicGeometry.Picard.RigidifiedClassesZariskiSeparatedProof

/-! # Relative cube criteria reduced to the field cube theorem -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

/-- The ordinary relative cube criterion follows from the field cube theorem:
the local two-axis and rigidified Zariski gluing inputs are published proofs. -/
theorem relativeCubeTriviality_of_fieldCubeTriviality
    (hF : FieldCubeTrivialityStatement.{u}) : RelativeCubeTrivialityStatement.{u} := by
  intro S _ A B C D h₁ h₂ h₃
  exact RelativeCubeAssembly.nonempty_iso_structureSheaf_of_faces A hF
    localTwoAxisTriviality rigidifiedClassesZariskiSeparated B C D h₁ h₂ h₃

/-- The ordinary relative cube criterion detects actual rigidified family classes,
using the published tensor-pullback preservation theorem. -/
theorem relativeRigidifiedCube_of_relativeCubeTriviality
    (hR : RelativeCubeTrivialityStatement.{u}) : RelativeRigidifiedCubeStatement.{u} := by
  intro S _ A B C q r hB hC
  exact rigidifiedClasses_eq_of_ordinaryCubeTriviality
    Langlands.Scheme.Modules.pullbackTensorComparisonIsIso A B C
    (hR S A B C) q r hB hC

/-- Relative detection of actual rigidified family classes has only the field cube
theorem as a remaining input. -/
theorem relativeRigidifiedCube_of_fieldCubeTriviality
    (hF : FieldCubeTrivialityStatement.{u}) : RelativeRigidifiedCubeStatement.{u} :=
  relativeRigidifiedCube_of_relativeCubeTriviality
    (relativeCubeTriviality_of_fieldCubeTriviality hF)

end Langlands.AbelianScheme
