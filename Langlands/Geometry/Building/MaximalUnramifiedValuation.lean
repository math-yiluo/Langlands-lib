import Langlands.Geometry.Building.IntegerValuation
import Langlands.Galois.Local.SeparableUnramifiedArithmeticProof

/-! # Normalized integer valuation on the actual maximal unramified field -/

noncomputable section

universe u

namespace Langlands.Geometry.Building.MaximalUnramified

open Langlands.LocalGalois.Separable

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]

local instance maximalUnramifiedValuationLocalInstance1 : ValuativeRel (inertiaFixedField F) :=
  ValuativeRel.ofValuation (fixedFieldValued F).v

local instance maximalUnramifiedValuationLocalInstance2 : Valuation.Compatible (fixedFieldValued F).v :=
  Valuation.Compatible.ofValuation _

local instance maximalUnramifiedValuationLocalInstance3 : ValuativeExtension F (inertiaFixedField F) :=
  ⟨fun a b => by
    rw [Valuation.vle_iff_le (fixedFieldValued F).v,
      Valuation.vle_iff_le (ValuativeRel.valuation F)]
    exact Valuation.HasExtension.val_map_le_iff
      (ValuativeRel.valuation F) (fixedFieldValuation F) a b⟩

/-- Normalize the intrinsic value group using the already proved value
attainment in the base field, followed by the base integer normalization. -/
def valueGroupEquiv :
    ValuativeRel.ValueGroupWithZero (inertiaFixedField F) ≃*o
      WithZero (Multiplicative ℤ) :=
  (fixedFieldValueGroupEquiv F (fixedFieldValuesFromBase F)).symm.trans
    (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F)

/-- The actual inertia fixed field, with a normalized integer-valued valuation.
This construction requires no local-field instance on the fixed field. -/
def valuation : Valuation (inertiaFixedField F) (WithZero (Multiplicative ℤ)) :=
  (ValuativeRel.valuation (inertiaFixedField F)).map
    (valueGroupEquiv F).toMonoidWithZeroHom
    (fun _ _ h => (map_le_map_iff (valueGroupEquiv F)).2 h)

theorem valuation_surjective : Function.Surjective (valuation F) :=
  (valueGroupEquiv F).surjective.comp ValuativeRel.valuation_surjective

theorem fixedFieldValueGroupEquiv_base (a : F) :
    fixedFieldValueGroupEquiv F (fixedFieldValuesFromBase F)
      (ValuativeRel.valuation F a) =
        ValuativeRel.valuation (inertiaFixedField F)
          (algebraMap F (inertiaFixedField F) a) := by
  change ValuativeExtension.mapValueGroupWithZero F (inertiaFixedField F)
    (ValuativeRel.valuation F a) = _
  exact ValuativeExtension.mapValueGroupWithZero_valuation a

/-- The new valuation extends exactly the existing normalized valuation,
including its normalization and its value at zero. -/
@[simp] theorem valuation_base (a : F) :
    valuation F (algebraMap F (inertiaFixedField F) a) =
      FML.normalizedMultiplicativeValuation F a := by
  change IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F
      ((fixedFieldValueGroupEquiv F (fixedFieldValuesFromBase F)).symm
        (ValuativeRel.valuation (inertiaFixedField F)
          (algebraMap F (inertiaFixedField F) a))) = _
  rw [← fixedFieldValueGroupEquiv_base F a, OrderMonoidIso.symm_apply_apply]
  rfl

theorem valuation_comap_base :
    (valuation F).comap (algebraMap F (inertiaFixedField F)) =
      FML.normalizedMultiplicativeValuation F := by
  ext a
  exact valuation_base F a

/-- Integer normalization preserves the full valuative relation induced by the
published spectral valuation. -/
theorem valuation_isEquiv :
    (valuation F).IsEquiv (fixedFieldValuation F) := by
  intro x y
  change valueGroupEquiv F (ValuativeRel.valuation (inertiaFixedField F) x) ≤
      valueGroupEquiv F (ValuativeRel.valuation (inertiaFixedField F) y) ↔ _
  rw [map_le_map_iff]
  exact ValuativeRel.isEquiv
    (ValuativeRel.valuation (inertiaFixedField F)) (fixedFieldValued F).v x y

/-- The integer-normalized valuation ring is literally the already published
subring of the same inertia fixed field. -/
theorem valuationSubring_eq :
    (valuation F).valuationSubring = fixedFieldIntegers F :=
  (Valuation.isEquiv_iff_valuationSubring _ _).mp (valuation_isEquiv F)

theorem mem_valuationSubring_iff (x : inertiaFixedField F) :
    x ∈ (valuation F).valuationSubring ↔ x ∈ fixedFieldIntegers F := by
  rw [valuationSubring_eq F]

/-- The resulting ring comparison is the identity under inclusion in the
actual inertia fixed field. -/
def integersEquiv :
    (valuation F).valuationSubring ≃+* fixedFieldIntegers F :=
  RingEquiv.subringCongr
    (congrArg ValuationSubring.toSubring (valuationSubring_eq F))

@[simp] theorem coe_integersEquiv (x : (valuation F).valuationSubring) :
    (integersEquiv F x : inertiaFixedField F) = (x : inertiaFixedField F) := rfl

/-- Exact equality of source-positive integer orders on base units. -/
@[simp] theorem orderUnits_base (a : Fˣ) :
    IntegerValuation.orderUnits (valuation F)
        (Units.map (algebraMap F (inertiaFixedField F)).toMonoidHom a) =
      IntegerValuation.orderUnits (FML.normalizedMultiplicativeValuation F) a := by
  change (IntegerValuation.orderUnits (valuation F) _).toAdd =
    (IntegerValuation.orderUnits (FML.normalizedMultiplicativeValuation F) a).toAdd
  rw [IntegerValuation.orderUnits_toAdd, IntegerValuation.orderUnits_toAdd]
  exact congrArg (fun z => -WithZero.log z) (valuation_base F a)

theorem orderUnits_comp_base :
    (IntegerValuation.orderUnits (valuation F)).comp
        (Units.map (algebraMap F (inertiaFixedField F)).toMonoidHom) =
      IntegerValuation.orderUnits (FML.normalizedMultiplicativeValuation F) := by
  ext a
  exact orderUnits_base F a

theorem orderUnits_base_eq_fieldOrderUnits (a : Fˣ) :
    IntegerValuation.orderUnits (valuation F)
        (Units.map (algebraMap F (inertiaFixedField F)).toMonoidHom a) =
      Plancherel.fieldOrderUnits F a := by
  rw [orderUnits_base, IntegerValuation.orderUnits_normalized]

/-- The real order supplied to apartments also restricts exactly to the base. -/
@[simp] theorem order_base (a : Fˣ) :
    IntegerValuation.order (valuation F)
        (Units.map (algebraMap F (inertiaFixedField F)).toMonoidHom a) =
      IntegerValuation.order (FML.normalizedMultiplicativeValuation F) a := by
  unfold IntegerValuation.order
  rw [orderUnits_base]

end Langlands.Geometry.Building.MaximalUnramified
