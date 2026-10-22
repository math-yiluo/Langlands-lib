import Langlands.ClassFieldTheory.Local.UnitNormStatement
import Langlands.ClassFieldTheory.Local.NormOrderProof
import Langlands.ClassFieldTheory.Local.UnitNormProof

/-! # Unramified norm membership

Combine the published norm-order formula and norm surjectivity on units
to characterize the full norm subgroup by divisibility of normalized order.
-/

noncomputable section

namespace Langlands.PadicField.TopologicalData

universe u
variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)

/-- An element of normalized order zero belongs to the actual zeroth unit filtration. -/
private theorem mem_unitFiltration_zero_of_ord_eq_zero (a : F.Carrierˣ)
    (ha : T.ord (a : F.Carrier) = 0) : a ∈ T.unitFiltration 0 := by
  have haInt : (a : F.Carrier) ∈ T.Integers := by
    apply (T.normalizedAbs_le_one_iff_mem_integers _).mp
    rw [T.normalizedAbs_of_ne_zero a.ne_zero, ha]
    simp
  have hiInt : (a : F.Carrier)⁻¹ ∈ T.Integers := by
    apply (T.normalizedAbs_le_one_iff_mem_integers _).mp
    rw [T.normalizedAbs_of_ne_zero (inv_ne_zero a.ne_zero), T.ord_inv, ha]
    simp
  let b : T.Integersˣ :=
    { val := ⟨a, haInt⟩
      inv := ⟨(a : F.Carrier)⁻¹, hiInt⟩
      val_inv := Subtype.ext (mul_inv_cancel₀ a.ne_zero)
      inv_val := Subtype.ext (inv_mul_cancel₀ a.ne_zero) }
  refine ⟨b, ?_, ?_⟩
  · change T.truncatedUnitsReduction 0 b = 1
    apply Units.ext
    change Ideal.Quotient.mk _ (b : T.Integers) = 1
    rw [← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq]
    simp
  · apply Units.ext
    rfl

end Langlands.PadicField.TopologicalData

namespace Langlands.LocalClassField

universe u v
variable {p : ℕ} [Fact p.Prime]
  {F : PadicField.{u} p} {E : PadicField.{v} p}
  [Algebra F.Carrier E.Carrier]
  [FiniteDimensional F.Carrier E.Carrier]
  (T : F.TopologicalData) (S : E.TopologicalData)

/-- The elementary deduction from a norm-order formula and surjectivity at the
zeroth unit-filtration level. -/
theorem normMembership_of_order_and_unitNorms
    (horder : ∀ b : E.Carrierˣ,
      T.ord (normUnits F.Carrier E.Carrier b : F.Carrier) =
        (Module.finrank F.Carrier E.Carrier : ℤ) * S.ord (b : E.Carrier))
    (hunit : (S.unitFiltration 0).map (normUnits F.Carrier E.Carrier) =
      T.unitFiltration 0) (a : F.Carrierˣ) :
    a ∈ normSubgroup F.Carrier E.Carrier ↔
      (Module.finrank F.Carrier E.Carrier : ℤ) ∣ T.ord (a : F.Carrier) := by
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨S.ord (b : E.Carrier), horder b⟩
  · rintro ⟨k, hk⟩
    obtain ⟨x, hx, hxord⟩ := S.ord_surjective_nonzero k
    let b : E.Carrierˣ := Units.mk0 x hx
    have hb : S.ord (b : E.Carrier) = k := hxord
    have hc : T.ord ((a / normUnits F.Carrier E.Carrier b : F.Carrierˣ) :
        F.Carrier) = 0 := by
      rw [Units.val_div_eq_div_val, div_eq_mul_inv]
      rw [T.ord_mul a.ne_zero (inv_ne_zero (normUnits F.Carrier E.Carrier b).ne_zero),
        T.ord_inv, horder, hb, hk]
      exact add_neg_cancel _
    have hcunit := T.mem_unitFiltration_zero_of_ord_eq_zero
      (a / normUnits F.Carrier E.Carrier b) hc
    rw [← hunit] at hcunit
    obtain ⟨c, _, hc⟩ := hcunit
    refine ⟨c * b, ?_⟩
    rw [map_mul, hc, div_mul_cancel]

/-- In an unramified extension, a field unit is a norm exactly when its
normalized order is divisible by the extension degree. -/
theorem unramifiedNormMembership : UnramifiedNormMembership.{u, v} := by
  intro p hp F E _ _ _ T S he a
  exact normMembership_of_order_and_unitNorms T S
    (ord_normUnits_of_unramified F E T S he)
    (unramifiedUnitNorms p F E T S he 0) a

end Langlands.LocalClassField
