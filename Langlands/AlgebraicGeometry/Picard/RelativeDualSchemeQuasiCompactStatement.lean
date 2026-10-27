import Langlands.AlgebraicGeometry.Picard.DualScheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Quasi-compactness of the chosen dual parameter scheme over a quasi-separated base -/

universe u

open AlgebraicGeometry

namespace Langlands.AbelianScheme

/-- Over a quasi-separated base, the structural morphism of the actual chosen universal
Picard-zero parameter scheme is quasi-compact. -/
def RelativeDualSchemeQuasiCompactStatement : Prop :=
  ∀ (S : Scheme.{u}) [QuasiSeparatedSpace S] (A : AbelianScheme S)
    (hA : HasDualScheme A), QuasiCompact (dualScheme A hA).hom

end Langlands.AbelianScheme
