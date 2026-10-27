import Langlands.AlgebraicGeometry.Picard.DualScheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.ValuativeCriterion

/-! # Valuative existence for the chosen dual parameter scheme over a quasi-separated base -/

universe u

open AlgebraicGeometry

namespace Langlands.AbelianScheme

/-- Over a quasi-separated base, the structural morphism of the actual chosen universal
Picard-zero parameter scheme satisfies the existence part of the valuative criterion. -/
def RelativeDualSchemeValuativeExistenceStatement : Prop :=
  ∀ (S : Scheme.{u}) [QuasiSeparatedSpace S] (A : AbelianScheme S)
    (hA : HasDualScheme A), ValuativeCriterion.Existence (dualScheme A hA).hom

end Langlands.AbelianScheme
