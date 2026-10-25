import Langlands.AlgebraicGeometry.Picard.DualScheme

/-! # A surjection from an abelian variety onto its chosen dual parameter scheme -/

universe u

open AlgebraicGeometry

namespace Langlands.AbelianScheme

/-- A chosen universal geometric Picard-zero parameter scheme over a field receives a
surjective morphism over the field from the abelian variety. -/
def FieldDualSchemeSurjectionStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (A : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))
    (hA : HasDualScheme A),
    ∃ f : A.X ⟶ dualScheme A hA, Surjective f.left

end Langlands.AbelianScheme
