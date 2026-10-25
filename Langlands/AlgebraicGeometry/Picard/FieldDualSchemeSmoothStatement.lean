import Langlands.AlgebraicGeometry.Picard.DualScheme

/-! # Smoothness of a chosen dual parameter scheme over a field -/

universe u

open AlgebraicGeometry

namespace Langlands.AbelianScheme

/-- A chosen universal geometric Picard-zero parameter scheme over a field is smooth. -/
def FieldDualSchemeSmoothStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (A : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))
    (hA : HasDualScheme A),
    Smooth (dualScheme A hA).hom

end Langlands.AbelianScheme
