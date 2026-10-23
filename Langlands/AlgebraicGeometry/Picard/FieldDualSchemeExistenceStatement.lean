import Langlands.AlgebraicGeometry.Picard.DualScheme

/-! # Existence target for a dual parameter scheme over a field -/

universe u

open AlgebraicGeometry

namespace Langlands.AbelianScheme

/-- Over a field, an abelian scheme has an actual universal geometric Picard-zero family. -/
def FieldDualSchemeExistenceStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (A : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))),
    HasDualScheme A

end Langlands.AbelianScheme
