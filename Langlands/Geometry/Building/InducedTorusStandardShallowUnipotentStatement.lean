import Langlands.Geometry.Building.KPLocalTorusCharacterFiltration
import Langlands.GroupScheme.IntegralModelReduction
import Langlands.GroupScheme.Reductive.Basic

/-! # Unipotence of shallow standard special fibres of induced tori -/

universe u

open AlgebraicGeometry
open Langlands.GroupScheme Langlands.LocalGalois.Separable
open scoped NNReal

namespace Langlands.Geometry.Building

/-- The shallow unipotence consequence of Kaletha–Prasad, Proposition
B.3.6(2), over the maximal unramified field. -/
def InducedTorusStandardShallowUnipotentStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (S : CommGroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
    [IsAffine S.X.left] (hS : IsTorus S.toGrp) (r : ℝ≥0)
    (M : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) S.toGrp),
    IsInducedTorus S → 0 < r → r < 1 → M.IsSmooth →
      M.integralPoints = localTorusFiltration F S hS r →
        IsUnipotent M.specialFibre

end Langlands.Geometry.Building
