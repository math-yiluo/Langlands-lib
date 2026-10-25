import Langlands.AlgebraicGeometry.Picard.DualScheme
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Properness of the chosen dual parameter scheme over a quasi-separated base -/

universe u

open AlgebraicGeometry

namespace Langlands.AbelianScheme

/-- Over a quasi-separated base, the actual chosen universal Picard-zero parameter scheme
is proper over the base. -/
def RelativeDualSchemeProperStatement : Prop :=
  ∀ (S : Scheme.{u}) [QuasiSeparatedSpace S] (A : AbelianScheme S)
    (hA : HasDualScheme A), IsProper (dualScheme A hA).hom

end Langlands.AbelianScheme
