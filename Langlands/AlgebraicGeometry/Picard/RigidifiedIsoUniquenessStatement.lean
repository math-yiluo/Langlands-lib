import Langlands.AlgebraicGeometry.Picard.RelativePicardZero

/-! # Uniqueness of actual rigidified abelian-scheme isomorphisms -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

/-- Any two rigidified isomorphisms between actual relative rigidified line
bundles are equal, for every abelian scheme and every test scheme. -/
def RigidifiedIsoUniquenessStatement : Prop :=
  ∀ (S : Scheme.{u}) (A : AbelianScheme S) (T : Over S)
    (L M : RigidifiedFamily A T), Subsingleton (L ≅ M)

end Langlands.AbelianScheme
