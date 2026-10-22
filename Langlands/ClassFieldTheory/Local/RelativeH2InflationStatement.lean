import Langlands.ClassFieldTheory.Local.Cohomology

/-! # Degree-two inflation and restriction in finite Galois towers -/

namespace Langlands.ClassFieldTheory.Local

universe u

/-- The actual degree-two inflation is injective, and its image is exactly
    the kernel of actual restriction, in every finite Galois tower. -/
def FiniteRelativeH2InflationExactness : Prop :=
  ∀ (K L M : Type u) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional K M]
    [IsGalois K L] [IsGalois K M],
    Function.Injective (relativeInflation K L M 2) ∧
      LinearMap.range (relativeInflation K L M 2).hom =
        LinearMap.ker (relativeRestriction K L M 2).hom

end Langlands.ClassFieldTheory.Local
