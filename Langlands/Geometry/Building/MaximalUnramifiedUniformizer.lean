import Langlands.Geometry.Building.MaximalUnramifiedValuation
import Langlands.Geometry.Building.SplitTorusValuation

/-! # A unit of order one in the actual maximal unramified field -/

noncomputable section

universe u

open Langlands.GroupScheme Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building.MaximalUnramified

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]

/-- The chosen base-field uniformizer, mapped as a unit to the actual inertia fixed field. -/
def baseUniformizerUnit : (inertiaFixedField F)ˣ :=
  Units.map (algebraMap F (inertiaFixedField F)).toMonoidHom
    (SplitTorusValuation.uniformizerUnit F)

/-- The source-positive integer order of the mapped uniformizer is one. -/
@[simp] theorem orderUnits_baseUniformizerUnit :
    (IntegerValuation.orderUnits (valuation F) (baseUniformizerUnit F)).toAdd = 1 := by
  rw [baseUniformizerUnit, orderUnits_base_eq_fieldOrderUnits,
    SplitTorusValuation.fieldOrderUnits_uniformizerUnit]

/-- The real order supplied to the apartment takes value one on the mapped uniformizer. -/
@[simp] theorem order_baseUniformizerUnit :
    IntegerValuation.order (valuation F) (baseUniformizerUnit F) = 1 := by
  unfold IntegerValuation.order
  rw [orderUnits_baseUniformizerUnit, Int.cast_one]

/-- The normalized maximal-unramified valuation has a unit of source-positive order one. -/
theorem exists_order_eq_one :
    ∃ t : (inertiaFixedField F)ˣ, IntegerValuation.order (valuation F) t = 1 :=
  ⟨baseUniformizerUnit F, order_baseUniformizerUnit F⟩

end Langlands.Geometry.Building.MaximalUnramified
