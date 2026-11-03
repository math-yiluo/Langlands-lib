import Langlands.GroupScheme.Rational.CenterSplitComponent
import Langlands.GroupScheme.Reductive.Basic
import Mathlib.NumberTheory.LocalField.Basic

/-! # Comparing the scheme center with the abstract rational-point center -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {F : Type u} [CommRing F]

/-- The necessary comparison is equality as subgroups of the same actual point group.
Its forward inclusion is already available; its reverse inclusion is a separate target. -/
def RationalCenterComparison (M : GroupScheme (Spec (CommRingCat.of F))) : Prop :=
  schemeCenterPoints M = Subgroup.center (rationalPoints M)

/-- The full scheme center evaluated on `F` equals the abstract center of `M(F)` for
every actual connected reductive group over every nonarchimedean local field. -/
def RationalCenterComparisonStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (M : GroupScheme (Spec (CommRingCat.of F))),
    IsConnectedReductive M → RationalCenterComparison M

end Langlands.GroupScheme
