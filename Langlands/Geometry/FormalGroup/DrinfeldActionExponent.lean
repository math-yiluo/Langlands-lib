import Langlands.Geometry.FormalGroup.DivisionOrder
import Langlands.Representation.Plancherel.LocalFieldUnits
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-! # The signed exponent in the Drinfeld group action -/

noncomputable section

universe u

namespace Langlands.FormalGroup.LocalDivision.DrinfeldAction

open ValuativeRel CentralDivision CentralSimple
open scoped WithZero TensorProduct

variable (K D : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]

/-- The normalized order of the actual reduced norm on division units. -/
def divisionUnitOrder : Dˣ →* Multiplicative ℤ :=
  (Plancherel.fieldOrderUnits K).comp ((reducedNormUnits K D K).comp
    (Units.map (Algebra.TensorProduct.includeRight : D →ₐ[K] K ⊗[K] D).toMonoidHom))

/-- This order is the negative logarithm of the original discrete division valuation. -/
theorem divisionUnitOrder_toAdd (g : Dˣ) :
    (divisionUnitOrder K D g).toAdd = -WithZero.log (localReducedNormIntValuation K D (g : D)) := by
  rw [divisionUnitOrder, MonoidHom.comp_apply, Plancherel.fieldOrderUnits_toAdd]
  rfl

/-- The exponent for inverse residue Frobenius is determinant order plus reduced-norm order. -/
def exponentHom : GL (Fin (reducedDegree K D)) K × Dˣ →* Multiplicative ℤ where
  toFun g := Plancherel.fieldOrderUnits K (Matrix.GeneralLinearGroup.det g.1) * divisionUnitOrder K D g.2
  map_one' := by
    change Plancherel.fieldOrderUnits K (Matrix.GeneralLinearGroup.det 1) * divisionUnitOrder K D 1 = 1
    simp
  map_mul' g h := by
    change Plancherel.fieldOrderUnits K (Matrix.GeneralLinearGroup.det (g.1 * h.1)) *
        divisionUnitOrder K D (g.2 * h.2) =
      (Plancherel.fieldOrderUnits K (Matrix.GeneralLinearGroup.det g.1) * divisionUnitOrder K D g.2) *
        (Plancherel.fieldOrderUnits K (Matrix.GeneralLinearGroup.det h.1) * divisionUnitOrder K D h.2)
    simp only [map_mul]
    ac_rfl

/-- The signed exponent on the original pair of actual groups. -/
abbrev exponent (g : GL (Fin (reducedDegree K D)) K × Dˣ) : ℤ :=
  (exponentHom K D g).toAdd

/-- The exponent has exactly the sum of the two normalized integer orders. -/
theorem exponent_eq (g : GL (Fin (reducedDegree K D)) K × Dˣ) :
    exponent K D g = (Plancherel.fieldOrderUnits K (Matrix.GeneralLinearGroup.det g.1)).toAdd +
      (divisionUnitOrder K D g.2).toAdd := rfl

@[simp]
theorem exponent_one : exponent K D 1 = 0 :=
  congrArg Multiplicative.toAdd ((exponentHom K D).map_one)

@[simp]
theorem exponent_mul (g h : GL (Fin (reducedDegree K D)) K × Dˣ) :
    exponent K D (g * h) = exponent K D g + exponent K D h :=
  congrArg Multiplicative.toAdd ((exponentHom K D).map_mul g h)

@[simp]
theorem exponent_inv (g : GL (Fin (reducedDegree K D)) K × Dˣ) :
    exponent K D g⁻¹ = -exponent K D g :=
  congrArg Multiplicative.toAdd ((exponentHom K D).map_inv g)

/-- An integral division-order unit has zero normalized reduced-norm order. -/
@[simp]
theorem divisionUnitOrder_integerUnit (a : (IntegerRing K D)ˣ) :
    (divisionUnitOrder K D (integerUnit K D a)).toAdd = 0 := by
  have h := (DivisionValuation.isUnit_iff_value_eq_one (localReducedNormValuation K D)
    (a : IntegerRing K D)).mp a.isUnit
  rw [divisionUnitOrder_toAdd]
  change -WithZero.log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
    (localReducedNormValuation K D ((a : IntegerRing K D) : D))) = 0
  rw [h, map_one, WithZero.log_one, neg_zero]

/-- Every division unit of order zero comes from an actual unit of the integer order. -/
theorem divisionUnitOrder_eq_zero_iff (g : Dˣ) :
    (divisionUnitOrder K D g).toAdd = 0 ↔ ∃ a : (IntegerRing K D)ˣ, integerUnit K D a = g := by
  constructor
  · intro h
    rw [divisionUnitOrder_toAdd] at h
    have he : localReducedNormIntValuation K D (g : D) = 1 := by
      rw [← WithZero.exp_log ((localReducedNormIntValuation K D).ne_zero_iff.mpr g.ne_zero),
        neg_eq_zero.mp h, WithZero.exp_zero]
    have hv : localReducedNormValuation K D (g : D) = 1 := by
      apply (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).injective
      change localReducedNormIntValuation K D (g : D) = _
      rw [he, map_one]
    let a : IntegerRing K D := ⟨g, hv.le⟩
    have ha : IsUnit a :=
      (DivisionValuation.isUnit_iff_value_eq_one (localReducedNormValuation K D) a).mpr hv
    exact ⟨ha.unit, Units.ext (congrArg Subtype.val ha.unit_spec)⟩
  · rintro ⟨a, rfl⟩
    exact divisionUnitOrder_integerUnit K D a

/-- On central scalars the reduced-norm order is the reduced degree times the scalar order. -/
theorem divisionUnitOrder_scalar (a : Kˣ) :
    (divisionUnitOrder K D (Units.map (algebraMap K D).toMonoidHom a)).toAdd =
      (reducedDegree K D : ℤ) * (Plancherel.fieldOrderUnits K a).toAdd := by
  rw [divisionUnitOrder_toAdd]
  change -WithZero.log (localReducedNormIntValuation K D (algebraMap K D (a : K))) = _
  rw [localReducedNormIntValuation_algebraMap, WithZero.log_pow, Plancherel.fieldOrderUnits_toAdd]
  change -((reducedDegree K D) • WithZero.log (FML.normalizedMultiplicativeValuation K (a : K))) = _
  rw [nsmul_eq_mul, mul_neg]

/-- Correcting the reduced-degree power by a normalized scalar gives an actual integral unit. -/
theorem exists_divisionUnitOrder_correction (g : Dˣ) (t : Kˣ)
    (ht : (Plancherel.fieldOrderUnits K t).toAdd = 1) :
    ∃ a : (IntegerRing K D)ˣ, integerUnit K D a =
      (Units.map (algebraMap K D).toMonoidHom t) ^ (-(divisionUnitOrder K D g).toAdd) *
        g ^ reducedDegree K D := by
  apply (divisionUnitOrder_eq_zero_iff K D _).mp
  rw [map_mul, map_zpow, map_pow]
  change -(divisionUnitOrder K D g).toAdd •
      (divisionUnitOrder K D (Units.map (algebraMap K D).toMonoidHom t)).toAdd +
    reducedDegree K D • (divisionUnitOrder K D g).toAdd = 0
  rw [divisionUnitOrder_scalar, ht, mul_one]
  simp [mul_comm]

/-- The exponent is zero on the actual integral division-order factor. -/
@[simp]
theorem exponent_integerUnit (a : (IntegerRing K D)ˣ) :
    exponent K D (1, integerUnit K D a) = 0 := by
  rw [exponent_eq]
  simp

/-- The determinant and reduced-norm contributions cancel on opposite central scalars. -/
@[simp]
theorem exponent_central (a : Kˣ) :
    exponent K D (Matrix.GeneralLinearGroup.scalar (Fin (reducedDegree K D)) a,
      Units.map (algebraMap K D).toMonoidHom a⁻¹) = 0 := by
  rw [exponent_eq]
  simp
  let n := (reducedDegree K D : ℤ) * (Plancherel.fieldOrderUnits K a).toAdd
  exact (congrArg (fun i : ℤ => n + -i) (divisionUnitOrder_scalar K D a)).trans
    (add_neg_cancel n)

end Langlands.FormalGroup.LocalDivision.DrinfeldAction
