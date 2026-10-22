import Langlands.ClassFieldTheory.Local.Corestriction

/-! # Degree-two relative corestriction after restriction -/

namespace Langlands.ClassFieldTheory.Local

universe u

/-- In every finite tower with `M` Galois over both lower fields, actual
degree-two corestriction after actual restriction is multiplication by the
degree of the middle field. The middle field need not be normal over the base. -/
def RelativeH2CorestrictionRestrictionStatement : Prop :=
  ∀ (K L M : Type u) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional K M] [FiniteDimensional L M]
    [IsGalois K M] [IsGalois L M],
    ∀ x : relativeCohomology K M 2,
      relativeCorestriction K L M 2 (relativeRestriction K L M 2 x) =
        Module.finrank K L • x

end Langlands.ClassFieldTheory.Local
