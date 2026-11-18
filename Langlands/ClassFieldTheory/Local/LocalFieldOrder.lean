import Langlands.LocalFactor.FML.Valuation
import Mathlib.NumberTheory.LocalField.Basic

noncomputable section

open ValuativeRel
open scoped WithZero

namespace Langlands.ClassFieldTheory.Local

universe u v

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The intrinsic valuation in the multiplicative copy of the integers with zero. -/
def discreteLocalValuation : Valuation K ℤᵐ⁰ :=
  Langlands.FML.normalizedMultiplicativeValuation K

instance discreteLocalValuation_compatible : (discreteLocalValuation K).Compatible where
  vle_iff_le _ _ := (Valuation.vle_iff_le (valuation K)).trans
    (map_le_map_iff (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)).symm

theorem discreteLocalValuation_surjective : Function.Surjective (discreteLocalValuation K) :=
  (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).surjective.comp valuation_surjective

/-- The additive normalized order on the actual group of field units. -/
def normalizedUnitOrder : Additive Kˣ →+ ℤ where
  toFun a := -WithZero.log (discreteLocalValuation K (a.toMul : K))
  map_zero' := by simp
  map_add' a b := by
    change -WithZero.log (discreteLocalValuation K ((a.toMul : K) * (b.toMul : K))) = _
    rw [map_mul, WithZero.log_mul ((map_ne_zero _).mpr a.toMul.ne_zero)
      ((map_ne_zero _).mpr b.toMul.ne_zero), neg_add_rev, add_comm]

theorem discreteLocalValuation_of_unit (a : Kˣ) :
    discreteLocalValuation K (a : K) = WithZero.exp (-normalizedUnitOrder K (.ofMul a)) := by
  change _ = WithZero.exp (- -WithZero.log (discreteLocalValuation K (a : K)))
  rw [neg_neg, WithZero.exp_log ((map_ne_zero _).mpr a.ne_zero)]

theorem normalizedUnitOrder_nonneg_iff (a : Kˣ) :
    0 ≤ normalizedUnitOrder K (.ofMul a) ↔ (a : K) ≤ᵥ 1 := by
  rw [Valuation.vle_one_iff (discreteLocalValuation K), discreteLocalValuation_of_unit,
    WithZero.exp_le_one_iff, neg_nonpos]

theorem normalizedUnitOrder_pos_iff (a : Kˣ) :
    0 < normalizedUnitOrder K (.ofMul a) ↔ (a : K) <ᵥ 1 := by
  rw [Valuation.vlt_iff_lt (discreteLocalValuation K), map_one, discreteLocalValuation_of_unit,
    WithZero.exp_lt_one_iff, neg_neg_iff_pos]

theorem normalizedUnitOrder_eq_zero_iff (a : Kˣ) :
    normalizedUnitOrder K (.ofMul a) = 0 ↔ valuation K (a : K) = 1 := by
  rw [← (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).injective.eq_iff, map_one]
  change _ ↔ discreteLocalValuation K (a : K) = 1
  rw [discreteLocalValuation_of_unit, WithZero.exp_eq_one, neg_eq_zero]

theorem normalizedUnitOrder_surjective : Function.Surjective (normalizedUnitOrder K) := by
  intro n
  obtain ⟨x, hx⟩ := discreteLocalValuation_surjective K (WithZero.exp (-n))
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, map_zero] at hx
    exact WithZero.exp_ne_zero hx.symm
  refine ⟨.ofMul (Units.mk0 x hx0), ?_⟩
  change -WithZero.log (discreteLocalValuation K x) = n
  simp [hx]

/-- A field unit with normalized order one. Its value as a field element
is a uniformizer of the integer ring. -/
def localUniformizer : Kˣ :=
  (Classical.choose (normalizedUnitOrder_surjective K 1)).toMul

@[simp]
theorem normalizedUnitOrder_localUniformizer :
    normalizedUnitOrder K (.ofMul (localUniformizer K)) = 1 :=
  Classical.choose_spec (normalizedUnitOrder_surjective K 1)

section Extension

variable (L : Type v) [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]

private theorem normalizedUnitOrder_map_pos (a : Kˣ) :
    0 < normalizedUnitOrder L (.ofMul (Units.map (algebraMap K L) a)) ↔
      0 < normalizedUnitOrder K (.ofMul a) := by
  rw [normalizedUnitOrder_pos_iff, normalizedUnitOrder_pos_iff]
  change algebraMap K L (a : K) <ᵥ 1 ↔ (a : K) <ᵥ 1
  rw [← map_one (algebraMap K L), ValuativeExtension.vlt_iff_vlt]

/-- The positive index factor of the value groups of a compatible extension,
given by the upper order of a base uniformizer. -/
def localRamificationFactor : ℕ :=
  (normalizedUnitOrder L (.ofMul (Units.map (algebraMap K L) (localUniformizer K)))).toNat

private theorem normalizedUnitOrder_map_uniformizer_pos :
    0 < normalizedUnitOrder L (.ofMul (Units.map (algebraMap K L) (localUniformizer K))) := by
  rw [normalizedUnitOrder_map_pos, normalizedUnitOrder_localUniformizer]
  exact Int.zero_lt_one

theorem localRamificationFactor_pos : 0 < localRamificationFactor K L := by
  have h := normalizedUnitOrder_map_uniformizer_pos K L
  unfold localRamificationFactor
  omega

theorem normalizedUnitOrder_map_uniformizer :
    normalizedUnitOrder L (.ofMul (Units.map (algebraMap K L) (localUniformizer K))) =
      localRamificationFactor K L :=
  (Int.toNat_of_nonneg (normalizedUnitOrder_map_uniformizer_pos K L).le).symm

/-- Restriction of normalized order multiplies by the ramification factor.
Compatibility of valuative relations suffices, even without separability. -/
theorem normalizedUnitOrder_map (a : Kˣ) :
    normalizedUnitOrder L (.ofMul (Units.map (algebraMap K L) a)) =
      (localRamificationFactor K L : ℤ) * normalizedUnitOrder K (.ofMul a) := by
  let f : Additive Kˣ →+ Additive Lˣ := (Units.map (algebraMap K L).toMonoidHom).toAdditive
  let x : Additive Kˣ := .ofMul a
  let p : Additive Kˣ := .ofMul (localUniformizer K)
  let n := normalizedUnitOrder K x
  have hb : normalizedUnitOrder K (x - n • p) = 0 := by
    rw [map_sub, map_zsmul]
    change n - n • normalizedUnitOrder K (.ofMul (localUniformizer K)) = 0
    simp
  have hval := ValuativeExtension.mapValueGroupWithZero_valuation (A := K) (B := L)
    ((x - n • p).toMul : K)
  rw [(normalizedUnitOrder_eq_zero_iff K (x - n • p).toMul).mp hb, map_one] at hval
  have hb' : normalizedUnitOrder L (f (x - n • p)) = 0 :=
    (normalizedUnitOrder_eq_zero_iff L _).mpr hval.symm
  rw [map_sub, map_zsmul, map_sub, map_zsmul, sub_eq_zero] at hb'
  change normalizedUnitOrder L (f x) = _
  rw [hb']
  change n • normalizedUnitOrder L (.ofMul (Units.map (algebraMap K L)
    (localUniformizer K))) = _
  rw [normalizedUnitOrder_map_uniformizer, zsmul_eq_mul, mul_comm]
  rfl

end Extension

end Langlands.ClassFieldTheory.Local
