import Langlands.Geometry.Building.MaximalUnramifiedBuildingData
import Langlands.Geometry.Metric.KPDefinitions

/-! # Complete NPC metric input for actual unramified buildings -/

noncomputable section

universe u

open AlgebraicGeometry
open Langlands.GroupScheme Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

namespace IntegerValuationBuildingData

variable {k : Type u} [Field k]
    {v : Valuation k (WithZero (Multiplicative ℤ))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (B : IntegerValuationBuildingData v G)

/-- A complete NPC metric on the original quotient for which its existing
rational-point action is isometric. This structure supplies no existence. -/
structure CompleteNPCMetric where
  [metric : MetricSpace B.ReducedBuilding]
  [complete : CompleteSpace B.ReducedBuilding]
  nonpositivelyCurved : Metric.KP.IsNonpositivelyCurved B.ReducedBuilding
  [isometric : IsIsometricSMul (rationalPoints G) B.ReducedBuilding]

end IntegerValuationBuildingData

namespace MaximalUnramified

/-- The unproved complete NPC metric input on every supplied actual building
over the maximal unramified field. No descent or prior metric is assumed. -/
def CompleteNPCMetricStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
    [IsAffineHom G.X.hom] (B : BuildingData F G),
    Nonempty B.CompleteNPCMetric

end MaximalUnramified
end Langlands.Geometry.Building
