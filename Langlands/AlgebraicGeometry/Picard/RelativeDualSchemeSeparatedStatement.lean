import Langlands.AlgebraicGeometry.Picard.DualScheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Separatedness of the chosen dual parameter scheme over a quasi-separated base -/

universe u

open AlgebraicGeometry

namespace Langlands.AbelianScheme

/-- Over a quasi-separated base, the structural morphism of the actual chosen universal
Picard-zero parameter scheme is separated: its diagonal is a closed immersion. -/
def RelativeDualSchemeSeparatedStatement : Prop :=
  ∀ (S : Scheme.{u}) [QuasiSeparatedSpace S] (A : AbelianScheme S)
    (hA : HasDualScheme A), IsSeparated (dualScheme A hA).hom

end Langlands.AbelianScheme
