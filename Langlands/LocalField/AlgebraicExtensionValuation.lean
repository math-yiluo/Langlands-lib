import Langlands.LocalField.LogAdditiveValuation
import Langlands.Galois.Local.AbsoluteDefinitions
import Langlands.Representation.Plancherel.LocalFieldUnits

/-! # Normalized real additive valuation on an algebraic local-field extension -/

noncomputable section

universe u v

open scoped NNReal

namespace Langlands.LocalField

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

local instance : NontriviallyNormedField F := LocalGalois.localNormedField F
local instance : IsUltrametricDist F := LocalGalois.localNormedField_ultrametric F
local instance : CompleteSpace F := LocalGalois.localNormedField_complete F

private theorem localNorm_le_iff_ord_le (x y : F) :
    ‖x‖ ≤ ‖y‖ ↔ FML.ord F y ≤ FML.ord F x := by
  rw [LocalGalois.localNormedField_le, FML.ord_le_ord_iff]
  exact (Valuation.Compatible.vle_iff_le x y).symm

private theorem localNorm_eq_of_ord_eq {x y : F}
    (h : FML.ord F x = FML.ord F y) : ‖x‖ = ‖y‖ := by
  apply le_antisymm
  · exact (localNorm_le_iff_ord_le F x y).mpr h.ge
  · exact (localNorm_le_iff_ord_le F y x).mpr h.le

private theorem uniformizer_norm_lt_one : ‖uniformizer F‖ < 1 := by
  have ho : FML.ord F 1 < FML.ord F (uniformizer F) := by simp
  have h : ‖uniformizer F‖ < ‖(1 : F)‖ := by
    rw [lt_iff_not_ge, localNorm_le_iff_ord_le F]
    exact not_le.mpr ho
  simpa using h

/-- The positive logarithmic scale determined by an actual order-one base element. -/
def localLogScale : ℝ := -Real.log ‖uniformizer F‖

theorem localLogScale_pos : 0 < localLogScale F := by
  exact neg_pos.mpr (Real.log_neg (norm_pos_iff.mpr (uniformizer_ne_zero F))
    (uniformizer_norm_lt_one F))

private theorem uniformizerUnit_order :
    (Plancherel.fieldOrderUnits F (Units.mk0 (uniformizer F) (uniformizer_ne_zero F))).toAdd = 1 := by
  apply WithTop.coe_injective
  rw [← Plancherel.fieldOrderUnits_ord]
  exact ord_uniformizer F

private theorem localNorm_unit (a : Fˣ) :
    ‖(a : F)‖ = ‖uniformizer F‖ ^ (Plancherel.fieldOrderUnits F a).toAdd := by
  let p : Fˣ := Units.mk0 (uniformizer F) (uniformizer_ne_zero F)
  let n : ℤ := (Plancherel.fieldOrderUnits F a).toAdd
  have hp : (Plancherel.fieldOrderUnits F p).toAdd = 1 := uniformizerUnit_order F
  have hn : FML.ord F ((p ^ n : Fˣ) : F) = FML.ord F (a : F) := by
    rw [Plancherel.fieldOrderUnits_ord, Plancherel.fieldOrderUnits_ord, map_zpow,
      toAdd_zpow, hp]
    simp [n]
  have hn' := localNorm_eq_of_ord_eq F hn
  simpa only [Units.val_zpow_eq_zpow_val, norm_zpow, p, Units.val_mk0] using hn'.symm

private theorem localLog_unit (a : Fˣ) :
    -Real.log ‖(a : F)‖ / localLogScale F =
      ((Plancherel.fieldOrderUnits F a).toAdd : ℝ) := by
  rw [localNorm_unit F, Real.log_zpow]
  dsimp [localLogScale]
  have hc : -Real.log ‖uniformizer F‖ ≠ 0 := ne_of_gt (localLogScale_pos F)
  calc
    -(↑(Plancherel.fieldOrderUnits F a).toAdd * Real.log ‖uniformizer F‖) /
        -Real.log ‖uniformizer F‖ =
      (↑(Plancherel.fieldOrderUnits F a).toAdd * -Real.log ‖uniformizer F‖) /
        -Real.log ‖uniformizer F‖ := by congr 1; ring
    _ = _ := mul_div_cancel_right₀ _ hc

variable (L : Type v) [Field L] [Algebra F L] [Algebra.IsAlgebraic F L]

/-- The actual spectral valuation, normalized additively to the base integer order. -/
def algebraicExtensionAddValuation : AddValuation L (WithTop ℝ) :=
  logAdditiveValuation (LocalGalois.spectralValuation F L) (localLogScale F) (localLogScale_pos F)

/-- Exact base-unit normalization, with the sign positive on the maximal ideal. -/
theorem algebraicExtensionAddValuation_base_unit (a : Fˣ) :
    algebraicExtensionAddValuation F L (algebraMap F L (a : F)) =
      (((Plancherel.fieldOrderUnits F a).toAdd : ℝ) : WithTop ℝ) := by
  rw [algebraicExtensionAddValuation,
    logAdditiveValuation_of_ne_zero _ _ _ ((map_ne_zero (algebraMap F L)).mpr a.ne_zero)]
  change ((-Real.log (spectralNorm F L (algebraMap F L (a : F))) / localLogScale F : ℝ) :
    WithTop ℝ) = _
  rw [spectralNorm_extends, localLog_unit F]

/-- Every base element of finite integer order has exactly that real additive value. -/
theorem algebraicExtensionAddValuation_base_of_ord_eq {x : F} {n : ℤ}
    (hx : FML.ord F x = (n : WithTop ℤ)) :
    algebraicExtensionAddValuation F L (algebraMap F L x) = ((n : ℝ) : WithTop ℝ) := by
  have hx0 : x ≠ 0 := (FML.ord_ne_top_iff F).mp (by rw [hx]; simp)
  have ho : (Plancherel.fieldOrderUnits F (Units.mk0 x hx0)).toAdd = n := by
    apply WithTop.coe_injective
    rw [← Plancherel.fieldOrderUnits_ord]
    exact hx
  simpa only [Units.val_mk0, ho] using
    algebraicExtensionAddValuation_base_unit F L (Units.mk0 x hx0)

/-- All base-field algebra automorphisms preserve the normalized extension valuation. -/
theorem algebraicExtensionAddValuation_invariant (σ : L ≃ₐ[F] L) (x : L) :
    algebraicExtensionAddValuation F L (σ x) = algebraicExtensionAddValuation F L x := by
  apply logAdditiveValuation_invariant
  intro y
  apply NNReal.eq
  exact (spectralNorm_eq_of_equiv (K := F) σ y).symm

end Langlands.LocalField
