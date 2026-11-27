import Langlands.LocalField.UniformizerUnitDecompositionStatement
import Langlands.Representation.Plancherel.LocalFieldUnits

/-! # Decomposition of a field unit by a uniformizer -/

namespace Langlands.LocalField

universe u

theorem uniformizerUnitDecomposition (F : Type u) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] :
    UniformizerUnitDecompositionStatement F := by
  intro π hπ
  let v := Plancherel.fieldOrderUnits F
  have hvπ : v π = Multiplicative.ofAdd 1 := by
    change (v π).toAdd = 1
    rw [Plancherel.fieldOrderUnits_ord F π] at hπ
    exact WithTop.coe_injective hπ
  have hpow (n : ℤ) : v (π ^ n) = Multiplicative.ofAdd n := by
    change (v (π ^ n)).toAdd = n
    rw [map_zpow, hvπ, toAdd_zpow]
    change n • (1 : ℤ) = n
    exact mul_one n
  have hunit {a : Fˣ} : a ∈ FML.unitGroup F ↔ v a = 1 := by
    rw [← Plancherel.fieldOrderUnits_ker F]
    rfl
  have horder (a : FML.unitGroup F) (n : ℤ) :
      v ((a : Fˣ) * π ^ n) = Multiplicative.ofAdd n := by
    rw [map_mul, hunit.mp a.property, hpow, one_mul]
  constructor
  · rintro ⟨a, m⟩ ⟨b, n⟩ hab
    change (a : Fˣ) * π ^ m = (b : Fˣ) * π ^ n at hab
    have hv := congrArg v hab
    rw [horder, horder] at hv
    have hmn := Multiplicative.ofAdd.injective hv
    subst n
    exact Prod.ext (Subtype.ext (mul_right_cancel hab)) rfl
  · intro a
    let n := (v a).toAdd
    have hu : a / π ^ n ∈ FML.unitGroup F := by
      apply hunit.mpr
      rw [map_div, hpow]
      exact div_self' (v a)
    exact ⟨(⟨a / π ^ n, hu⟩, n), div_mul_cancel a (π ^ n)⟩

end Langlands.LocalField
