import Langlands.AbelianScheme.Basic
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Closed immersions of abelian schemes of the same relative dimension -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

/-- A closed immersion between actual abelian schemes over a field, both smooth
of the same relative dimension, is an isomorphism of underlying schemes. -/
def FieldEqualDimensionClosedImmersionStatement : Prop :=
  ∀ (K : Type u) [Field K]
    (A B : AbelianScheme (Spec (CommRingCat.of K))) (g : ℕ),
    A.HasRelativeDimension g → B.HasRelativeDimension g →
    ∀ f : A ⟶ B, IsClosedImmersion (hom f) → IsIso (hom f)

end Langlands.AbelianScheme
