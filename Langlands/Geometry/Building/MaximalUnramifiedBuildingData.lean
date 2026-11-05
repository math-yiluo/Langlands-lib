import Langlands.Geometry.Building.MaximalUnramifiedValuation
import Langlands.Geometry.Building.IntegerValuationBuildingData

/-! # Building data over the actual maximal unramified field -/

noncomputable section

universe u

open AlgebraicGeometry
open Langlands.GroupScheme Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building.MaximalUnramified

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]

/-- Supplied KP building data over the actual inertia fixed field, using its
constructed integer-valued valuation. This type does not assert inhabitance. -/
abbrev BuildingData
    (G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
    [IsAffineHom G.X.hom] : Type (u + 1) :=
  IntegerValuationBuildingData (valuation F) G

/-- On base units, the real apartment order is exactly the existing local order. -/
theorem order_base_eq_localFieldOrder (a : Fˣ) :
    IntegerValuation.order (valuation F)
        (Units.map (algebraMap F (inertiaFixedField F)).toMonoidHom a) =
      localFieldOrder F a := by
  rw [order_base, IntegerValuation.order_normalized]

end Langlands.Geometry.Building.MaximalUnramified
