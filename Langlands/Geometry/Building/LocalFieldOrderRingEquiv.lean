import Langlands.Geometry.Building.FullValidity.Assignment
import Langlands.Geometry.Building.IntegerCentralizer
import Mathlib.Algebra.Group.Units.Equiv

/-! # Normalized local-field order under valuative ring equivalences -/

noncomputable section

namespace Langlands.Geometry.Building

universe u

private theorem integerOrderHom_unique {A : Type*} [Group A]
    (f g : A →* Multiplicative ℤ) (hf : Function.Surjective f)
    (hg : Function.Surjective g)
    (hle : ∀ a b, (g a).toAdd ≤ (g b).toAdd ↔ (f a).toAdd ≤ (f b).toAdd) :
    g = f := by
  obtain ⟨π, hπ⟩ := hf (Multiplicative.ofAdd 1)
  have heq {a b : A} (h : f a = f b) : g a = g b := by
    apply le_antisymm
    · exact (hle a b).mpr (le_of_eq h)
    · exact (hle b a).mpr (le_of_eq h.symm)
  have hc : 0 < (g π).toAdd := by
    have hn : ¬ (g π).toAdd ≤ (g 1).toAdd := by
      rw [hle, hπ, f.map_one]
      change ¬ (1 : ℤ) ≤ 0
      decide
    simpa using lt_of_not_ge hn
  have hlinear (a : A) : (g a).toAdd = (f a).toAdd * (g π).toAdd := by
    have h : f a = f (π ^ (f a).toAdd) := by
      rw [map_zpow, hπ]
      change (f a).toAdd = ((Multiplicative.ofAdd 1 : Multiplicative ℤ) ^ (f a).toAdd).toAdd
      rw [toAdd_zpow]
      change (f a).toAdd = (f a).toAdd * 1
      exact (mul_one _).symm
    have h' := congrArg Multiplicative.toAdd (heq h)
    simpa using h'
  obtain ⟨ρ, hρ⟩ := hg (Multiplicative.ofAdd 1)
  have hprod : (f ρ).toAdd * (g π).toAdd = 1 := by
    rw [← hlinear, hρ]
    rfl
  have hm : 0 < (f ρ).toAdd :=
    (mul_pos_iff_of_pos_right hc).mp (by rw [hprod]; decide)
  have hbound := mul_le_mul_of_nonneg_right (show 1 ≤ (f ρ).toAdd by omega)
    (le_of_lt hc)
  have hc1 : (g π).toAdd = 1 := by omega
  ext a
  have ha := hlinear a
  change (g a).toAdd = (f a).toAdd
  simpa [hc1] using ha

variable {F₁ F₂ : Type u} [Field F₁] [Field F₂]
  [ValuativeRel F₁] [ValuativeRel F₂] [TopologicalSpace F₁] [TopologicalSpace F₂]
  [IsNonarchimedeanLocalField F₁] [IsNonarchimedeanLocalField F₂]

/-- A valuative field isomorphism preserves the exact normalized integer order on units. -/
theorem fieldOrderUnits_ringEquiv (σ : F₁ ≃+* F₂) (hσ : IsValuativeRingEquiv σ)
    (t : F₁ˣ) :
    Plancherel.fieldOrderUnits F₂ (Units.map σ.toMonoidHom t) =
      Plancherel.fieldOrderUnits F₁ t := by
  have h := integerOrderHom_unique (Plancherel.fieldOrderUnits F₁)
    ((Plancherel.fieldOrderUnits F₂).comp (Units.map σ.toMonoidHom))
    (Plancherel.fieldOrderUnits_surjective F₁)
    ((Plancherel.fieldOrderUnits_surjective F₂).comp
      (Units.mapEquiv σ.toMulEquiv).surjective) (by
        intro a b
        change (Plancherel.fieldOrderUnits F₂ (Units.map σ.toMonoidHom a)).toAdd ≤
            (Plancherel.fieldOrderUnits F₂ (Units.map σ.toMonoidHom b)).toAdd ↔ _
        rw [← WithTop.coe_le_coe (α := ℤ),
          ← Plancherel.fieldOrderUnits_ord F₂, ← Plancherel.fieldOrderUnits_ord F₂,
          FML.ord_le_ord_iff]
        rw [← WithTop.coe_le_coe (α := ℤ),
          ← Plancherel.fieldOrderUnits_ord F₁, ← Plancherel.fieldOrderUnits_ord F₁,
          FML.ord_le_ord_iff]
        exact hσ _ _)
  exact congrArg (fun f => f t) h

/-- The real normalized order is unchanged by a valuative field isomorphism. -/
theorem localFieldOrder_ringEquiv (σ : F₁ ≃+* F₂) (hσ : IsValuativeRingEquiv σ)
    (t : F₁ˣ) :
    localFieldOrder F₂ (Units.map σ.toMonoidHom t) = localFieldOrder F₁ t := by
  unfold localFieldOrder
  rw [fieldOrderUnits_ringEquiv σ hσ]

/-- The normalized real unit order, bundled as a homomorphism. -/
def localFieldOrderHom (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] : Fˣ →* Multiplicative ℝ :=
  (Int.castAddHom ℝ).toMultiplicative.comp (Plancherel.fieldOrderUnits F)

@[simp]
theorem localFieldOrderHom_toAdd (F : Type u) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] (t : Fˣ) :
    (localFieldOrderHom F t).toAdd = localFieldOrder F t := rfl

/-- The integer-valuation apartment convention has the same field-isomorphism compatibility. -/
theorem normalizedIntegerOrder_ringEquiv (σ : F₁ ≃+* F₂) (hσ : IsValuativeRingEquiv σ)
    (t : F₁ˣ) :
    let : Algebra F₁ F₂ := σ.toRingHom.toAlgebra
    IntegerValuation.order (FML.normalizedMultiplicativeValuation F₂)
        (Units.map (algebraMap F₁ F₂).toMonoidHom t) =
      IntegerValuation.order (FML.normalizedMultiplicativeValuation F₁) t := by
  let : Algebra F₁ F₂ := σ.toRingHom.toAlgebra
  rw [IntegerValuation.order_normalized, IntegerValuation.order_normalized]
  exact localFieldOrder_ringEquiv σ hσ t

end Langlands.Geometry.Building
