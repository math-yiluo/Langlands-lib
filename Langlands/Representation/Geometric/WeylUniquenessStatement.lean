import Langlands.Representation.Geometric.WeylDefinitions

/-! The uniqueness component of the GL block Weyl double-coset statement. -/

namespace Langlands.Geometric

/-- Two minimal representatives in the same Weyl double coset are equal,
for every rank, including zero. -/
def WeylMinimalRepresentativeUniquenessTheorem : Prop :=
  ∀ (n : ℕ) (B C : GeneralLinear.BlockShape n),
    Function.Injective (weylDoubleCoset B C)

end Langlands.Geometric
