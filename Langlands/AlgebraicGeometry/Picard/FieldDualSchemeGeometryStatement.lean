import Langlands.AlgebraicGeometry.Picard.DualScheme

/-! # Geometric properties of a chosen dual parameter scheme over a field -/

universe u

open AlgebraicGeometry

namespace Langlands.AbelianScheme

/-- A chosen universal geometric Picard-zero parameter scheme over a field
is smooth, proper and geometrically connected. -/
def FieldDualSchemeGeometryStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (A : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))
    (hA : HasDualScheme A),
    Smooth (dualScheme A hA).hom ∧ IsProper (dualScheme A hA).hom ∧
      GeometricallyConnected (dualScheme A hA).hom

end Langlands.AbelianScheme
