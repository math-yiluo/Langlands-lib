import Langlands.Geometry.Building.KPLocalTorusCharacterFiltration
import Langlands.GroupScheme.IntegralModelReduction

/-! # First congruence subgroups of standard models of induced tori -/

universe u

open AlgebraicGeometry
open Langlands.GroupScheme Langlands.LocalGalois.Separable
open scoped NNReal

namespace Langlands.Geometry.Building

/-- Kaletha–Prasad, Proposition B.3.6(3), over the maximal unramified field.
For any smooth model realizing the standard point group at depth `r`, the
first congruence subgroup equals the standard point group at depth `r + 1`. -/
def InducedTorusStandardCongruenceStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (S : CommGroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
    [IsAffine S.X.left] (hS : IsTorus S.toGrp) (r : ℝ≥0)
    (M : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) S.toGrp),
    IsInducedTorus S → M.IsSmooth → M.integralPoints = localTorusFiltration F S hS r →
      M.congruenceSubgroup = localTorusFiltration F S hS (r + 1)

end Langlands.Geometry.Building
