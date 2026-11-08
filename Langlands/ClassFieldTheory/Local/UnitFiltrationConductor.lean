import Langlands.ClassFieldTheory.Local.GradedUnitCoordinates
import Langlands.ClassFieldTheory.Local.FiniteConductorStatement

/-! Comparison of the two actual unit filtrations and their conductor criterion. -/

noncomputable section

namespace Langlands.PadicField.TopologicalData

open scoped WithZero

universe u
variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)

theorem filtrationValuationIntegers : T.discreteValuation.Integers T.Integers := by
  refine ⟨Subtype.val_injective, ?_, ?_⟩
  · intro x
    exact (T.mem_integers_iff_discreteValuation_le_one x.val).mp x.property
  · intro x hx
    exact ⟨⟨x, (T.mem_integers_iff_discreteValuation_le_one x).mpr hx⟩, rfl⟩

/-- Ideal powers are exactly the actual discrete valuation balls, including power zero. -/
theorem mem_maximalIdeal_pow_iff_discreteValuation_le (n : ℕ) (a : T.Integers) :
    a ∈ IsLocalRing.maximalIdeal T.Integers ^ n ↔
      T.discreteValuation (a : F.Carrier) ≤ WithZero.exp (-(n : ℤ)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have hi : Irreducible (T.coordinateUniformizer T.uniformizer T.ord_uniformizer) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr
      (T.maximalIdeal_eq_span_coordinateUniformizer T.uniformizer T.ord_uniformizer)
  rw [← SetLike.mem_coe,
    T.filtrationValuationIntegers.maximalIdeal_pow_eq_setOfPred_le_v_algebraMap_pow hi]
  change T.discreteValuation (a : F.Carrier) ≤
      T.discreteValuation (T.coordinateUniformizer T.uniformizer T.ord_uniformizer : F.Carrier) ^ n ↔ _
  rw [T.coordinateUniformizer_coe, T.discreteValuation_uniformizer, ← WithZero.exp_nsmul]
  simp

/-- Every integral unit has discrete valuation one after inclusion in the field. -/
theorem discreteValuation_integerUnit (a : T.Integersˣ) :
    T.discreteValuation ((a : T.Integers) : F.Carrier) = 1 :=
  T.filtrationValuationIntegers.isUnit_iff_valuation_eq_one.mp a.isUnit

/-- The reduction-kernel and valuation definitions give the same literal subgroup. -/
theorem unitFiltration_eq_principalUnits (n : ℕ) :
    T.unitFiltration n = T.principalUnits n := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨T.discreteValuation_integerUnit a,
      (T.mem_maximalIdeal_pow_iff_discreteValuation_le n ((a : T.Integers) - 1)).mp
        ((T.mem_congruenceUnits_iff n a).mp ha)⟩
  · intro hx
    have hv : T.discreteValuation (↑(x⁻¹) : F.Carrier) = 1 := by
      simpa only [Units.val_inv_eq_inv_val, map_inv₀, inv_one] using
        congrArg Inv.inv hx.1
    let a : T.Integersˣ :=
      { val := ⟨(x : F.Carrier), (T.mem_integers_iff_discreteValuation_le_one _).mpr hx.1.le⟩
        inv := ⟨(↑(x⁻¹) : F.Carrier),
          (T.mem_integers_iff_discreteValuation_le_one _).mpr hv.le⟩
        val_inv := Subtype.ext (Units.val_inv x)
        inv_val := Subtype.ext (Units.inv_val x) }
    refine ⟨a, (T.mem_congruenceUnits_iff n a).mpr ?_, ?_⟩
    · exact (T.mem_maximalIdeal_pow_iff_discreteValuation_le n _).mpr hx.2
    · apply Units.ext
      rfl

/-- The actual integer-unit congruence kernel is canonically the valuation unit group. -/
def congruenceUnitsEquivPrincipalUnits (n : ℕ) :
    T.congruenceUnits n ≃* T.principalUnits n :=
  (T.congruenceUnitsEquivFiltration n).trans
    (MulEquiv.subgroupCongr (T.unitFiltration_eq_principalUnits n))

@[simp]
theorem congruenceUnitsEquivPrincipalUnits_coe (n : ℕ) (a : T.congruenceUnits n) :
    (T.congruenceUnitsEquivPrincipalUnits n a : F.Carrierˣ) =
      T.integerUnitsInclusion a := rfl

/-- The conductor bound is equivalent to containment of the actual reduction-kernel units. -/
theorem multiplicativeConductor_le_iff_unitFiltration_le_ker :
    letI := T.topology
    ∀ (χ : F.Carrierˣ →ₜ* ℂˣ) (n : ℕ),
      T.multiplicativeConductor χ ≤ n ↔ T.unitFiltration n ≤ χ.toMonoidHom.ker := by
  let := T.topology
  intro χ n
  rw [T.unitFiltration_eq_principalUnits,
    ← T.multiplicativeTrivialAt_iff_conductor_le]
  rfl

end Langlands.PadicField.TopologicalData

namespace Langlands.LocalClassField

universe u

/-- The complete unconditional comparison for every supplied local realization. -/
theorem unitFiltrationComparison : UnitFiltrationComparison.{u} := by
  intro p hp F T n
  exact T.unitFiltration_eq_principalUnits n

end Langlands.LocalClassField
