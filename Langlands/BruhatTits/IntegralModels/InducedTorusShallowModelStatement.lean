import Langlands.Geometry.Building.KPLocalTorusCharacterFiltration
import Langlands.GroupScheme.IntegralModelReduction

/-! # Smooth integral models of induced tori at shallow positive depth -/

universe u

open AlgebraicGeometry
open Langlands.Geometry.Building Langlands.GroupScheme Langlands.LocalGalois.Separable
open scoped NNReal

namespace Langlands.BruhatTits.IntegralModels

/-- The model-existence clause of Kaletha–Prasad, Proposition B.3.6(1), over the
maximal unramified field at depth `0 < r < 1`. The subgroup is the image of the
model's sections under its specified generic-fibre identification. -/
def InducedTorusShallowModelStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (R : CommGroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
    (r : ℝ≥0), IsInducedTorus R → 0 < r → r < 1 →
    ∃ M : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) R.toGrp,
      M.IsSmooth ∧ M.HasGeometricallyConnectedFibres ∧
        M.integralPoints = localGeometricCharacterCongruence F R r

end Langlands.BruhatTits.IntegralModels
