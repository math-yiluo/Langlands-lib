import Langlands.AlgebraicGeometry.Picard.DualScheme
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Local finite presentation of the chosen dual parameter scheme over a quasi-separated base -/

universe u

open AlgebraicGeometry

namespace Langlands.AbelianScheme

/-- Over a quasi-separated base, the actual chosen universal Picard-zero parameter scheme
is locally of finite presentation over the base. -/
def RelativeDualSchemeFinitePresentationStatement : Prop :=
  ∀ (S : Scheme.{u}) [QuasiSeparatedSpace S] (A : AbelianScheme S)
    (hA : HasDualScheme A), LocallyOfFinitePresentation (dualScheme A hA).hom

end Langlands.AbelianScheme
