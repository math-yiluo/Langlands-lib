import Langlands.AlgebraicGeometry.Picard.DualScheme
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Flatness of the chosen dual parameter scheme over a quasi-separated base -/

universe u

open AlgebraicGeometry

namespace Langlands.AbelianScheme

/-- Over a quasi-separated base, the actual chosen universal Picard-zero parameter scheme
is flat over the base. -/
def RelativeDualSchemeFlatStatement : Prop :=
  ∀ (S : Scheme.{u}) [QuasiSeparatedSpace S] (A : AbelianScheme S)
    (hA : HasDualScheme A), Flat (dualScheme A hA).hom

end Langlands.AbelianScheme
