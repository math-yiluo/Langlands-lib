import Langlands.GroupScheme.Absolute.SolvableSplitExtensionOneDimensional

/-! # Homomorphic splitting of the torus quotient of a solvable group -/

universe u

namespace Langlands.GroupScheme

/-- The torus quotient of a smooth connected solvable affine group over an algebraically
closed field has a section as a group-scheme homomorphism. -/
theorem solvableSplitExtension : SolvableSplitExtensionStatement.{u} :=
  solvableSplitExtension_of_oneDimensional perfectFieldOneDimensionalUnipotent

end Langlands.GroupScheme
