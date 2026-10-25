import Langlands.AlgebraicGeometry.Picard.DualScheme

/-! # Separatedness of a chosen dual parameter scheme over a field -/

universe u

open AlgebraicGeometry

namespace Langlands.AbelianScheme

/-- A chosen universal geometric Picard-zero parameter scheme over a field is separated. -/
def FieldDualSchemeSeparatedStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (A : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))
    (hA : HasDualScheme A),
    IsSeparated (dualScheme A hA).hom

end Langlands.AbelianScheme
