import Langlands.ClassFieldTheory.Local.ProfiniteReciprocityAssembly
import Langlands.ClassFieldTheory.Local.FiniteArtinSystemExistenceProof

/-!
# Existence and uniqueness of normalized profinite local reciprocity

The unconditional finite Artin-system theorem discharges the premise of the
published assembly from finite systems to continuous profinite maps.
-/

namespace Langlands.LocalClassField

universe u

/-- Every p-adic field with a supplied topological datum has exactly one
continuous homomorphism to the actual absolute-Galois abelianization satisfying
the geometric profinite reciprocity relation. -/
theorem profiniteReciprocityExistenceUniqueness :
    ProfiniteReciprocityExistenceUniqueness.{u} :=
  ProfiniteReciprocityAssembly.profiniteReciprocity_of_finiteArtin
    geometricFiniteArtinSystemExistenceUniqueness

end Langlands.LocalClassField
