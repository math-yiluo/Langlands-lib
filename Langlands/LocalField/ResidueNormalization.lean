import Langlands.LocalFactor.FML.Valuation
import Mathlib.Data.Int.WithZero
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.FieldTheory.Finite.Basic

/-! # Residue-normalized absolute value on an arbitrary nonarchimedean local field -/

open scoped WithZero NNReal

universe u

namespace Langlands.FML

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- The existing normalized multiplicative valuation is onto. -/
theorem normalizedMultiplicativeValuation_surjective :
    Function.Surjective (normalizedMultiplicativeValuation F) :=
  (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F).surjective.comp
    ValuativeRel.valuation_surjective

/-- Exact finite-order formula, without changing the convention at zero. -/
theorem ord_of_ne_zero {x : F} (hx : x ≠ 0) :
    ord F x = ((-WithZero.log (normalizedMultiplicativeValuation F x) : ℤ) : WithTop ℤ) := by
  change (if normalizedMultiplicativeValuation F x = 0 then ⊤ else _) = _
  rw [ite_eq_right ((normalizedMultiplicativeValuation F).ne_zero_iff.mpr hx)]

/-- Every finite order occurs at a nonzero element. -/
theorem ord_surjective_nonzero (n : ℤ) :
    ∃ x : F, x ≠ 0 ∧ ord F x = (n : WithTop ℤ) := by
  obtain ⟨x, hx⟩ := normalizedMultiplicativeValuation_surjective F (WithZero.exp (-n))
  have hx0 : x ≠ 0 := by
    intro h
    exact WithZero.exp_ne_zero (by rw [← hx, h, map_zero])
  refine ⟨x, hx0, ?_⟩
  simp [ord_of_ne_zero F hx0, hx]

/-- The order takes every value in `ℤ ∪ {∞}`. -/
theorem ord_surjective : Function.Surjective (ord F) := by
  intro n
  cases n with
  | top => exact ⟨0, ord_zero F⟩
  | coe n =>
      obtain ⟨x, _, hx⟩ := ord_surjective_nonzero F n
      exact ⟨x, hx⟩

/-- The actual maximal ideal is characterized by strictly positive order. -/
theorem mem_maximalIdeal_iff_ord_pos (x : ringOfIntegers F) :
    x ∈ IsLocalRing.maximalIdeal (ringOfIntegers F) ↔ 0 < ord F (x : F) := by
  rw [IsLocalRing.mem_maximalIdeal]
  change ¬IsUnit x ↔ _
  rw [Valuation.Integer.not_isUnit_iff_valuation_lt_one]
  rw [← (ValuativeRel.valuation F).vlt_one_iff, ← ord_lt_ord_iff F 1 (x : F)]
  simp

/-- The embedded integral-unit group consists exactly of the order-zero units. -/
theorem mem_unitGroup_iff_ord_eq_zero (x : Fˣ) :
    x ∈ unitGroup F ↔ ord F (x : F) = 0 := by
  constructor
  · exact ord_unitGroup F x
  · intro hx
    rw [Valuation.mem_unitGroup_iff]
    apply le_antisymm
    · rw [← (ValuativeRel.valuation F).vle_one_iff, ← ord_le_ord_iff F 1 (x : F)]
      simp [hx]
    · have h : (1 : F) ≤ᵥ (x : F) := (ord_le_ord_iff F (x : F) 1).mp (by simp [hx])
      simpa only [map_one] using (Valuation.Compatible.vle_iff_le (1 : F) (x : F)).mp h

end Langlands.FML

namespace Langlands.LocalField

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- The residue field of the actual valuation ring. -/
abbrev ResidueField := IsLocalRing.ResidueField (FML.ringOfIntegers F)

/-- The cardinality of the actual residue field. -/
noncomputable def residueCardinality : ℕ := Nat.card (ResidueField F)

/-- Local compactness and nontriviality imply finite residue field. -/
theorem finite_residueField : Finite (ResidueField F) := inferInstance

/-- A finite residue field has at least two elements. -/
theorem residueCardinality_gt_one : 1 < residueCardinality F := by
  let := Fintype.ofFinite (ResidueField F)
  simpa [residueCardinality, Nat.card_eq_fintype_card] using
    (Fintype.one_lt_card : 1 < Fintype.card (ResidueField F))

/-- A chosen actual field element of source-standard order one. -/
noncomputable def uniformizer : F := (FML.ord_surjective_nonzero F 1).choose

theorem uniformizer_ne_zero : uniformizer F ≠ 0 :=
  (FML.ord_surjective_nonzero F 1).choose_spec.1

@[simp] theorem ord_uniformizer : FML.ord F (uniformizer F) = 1 :=
  (FML.ord_surjective_nonzero F 1).choose_spec.2

private theorem residueCardinality_nnreal_gt_one :
    (1 : ℝ≥0) < (residueCardinality F : ℝ≥0) := by
  exact_mod_cast residueCardinality_gt_one F

/-- The actual normalized absolute value, obtained from Mathlib's exponential homomorphism. -/
noncomputable def residueNormalizedAbsoluteValue : AbsoluteValue F ℝ where
  toFun x := (WithZeroMulInt.toNNReal (residueCardinality_nnreal_gt_one F).ne_zero
    (FML.normalizedMultiplicativeValuation F x) : ℝ)
  map_mul' x y := by simp only [map_mul, NNReal.coe_mul]
  nonneg' x := NNReal.coe_nonneg _
  eq_zero' x := by simp only [NNReal.coe_eq_zero, map_eq_zero]
  add_le' x y := by
    have h := (WithZeroMulInt.toNNReal_strictMono
      (residueCardinality_nnreal_gt_one F)).monotone
    rcases le_max_iff.mp ((FML.normalizedMultiplicativeValuation F).map_add x y) with hx | hy
    · exact (NNReal.coe_le_coe.mpr (h hx)).trans (le_add_of_nonneg_right (NNReal.coe_nonneg _))
    · exact (NNReal.coe_le_coe.mpr (h hy)).trans (le_add_of_nonneg_left (NNReal.coe_nonneg _))

/-- The nonzero formula in multiplicative-valuation coordinates. -/
theorem residueNormalizedAbsoluteValue_of_ne_zero {x : F} (hx : x ≠ 0) :
    residueNormalizedAbsoluteValue F x =
      (residueCardinality F : ℝ) ^ WithZero.log (FML.normalizedMultiplicativeValuation F x) := by
  have hv := (FML.normalizedMultiplicativeValuation F).ne_zero_iff.mpr hx
  change (WithZeroMulInt.toNNReal _ _ : ℝ) = _
  rw [WithZeroMulInt.toNNReal_neg_apply _ hv, WithZero.toAdd_unzero_eq_log hv]
  simp

/-- Exact source formula for any finite additive order. -/
theorem residueNormalizedAbsoluteValue_of_ord_eq {x : F} {n : ℤ}
    (hx : FML.ord F x = (n : WithTop ℤ)) :
    residueNormalizedAbsoluteValue F x = (residueCardinality F : ℝ) ^ (-n) := by
  have hx0 : x ≠ 0 := (FML.ord_ne_top_iff F).mp (by rw [hx]; simp)
  have ho := hx
  rw [FML.ord_of_ne_zero F hx0, WithTop.coe_inj] at ho
  rw [residueNormalizedAbsoluteValue_of_ne_zero F hx0, ← ho, neg_neg]

/-- The ultrametric inequality is retained by the increasing exponential homomorphism. -/
theorem residueNormalizedAbsoluteValue_add_le_max (x y : F) :
    residueNormalizedAbsoluteValue F (x + y) ≤
      max (residueNormalizedAbsoluteValue F x) (residueNormalizedAbsoluteValue F y) := by
  have h := (WithZeroMulInt.toNNReal_strictMono
    (residueCardinality_nnreal_gt_one F)).monotone
  rcases le_max_iff.mp ((FML.normalizedMultiplicativeValuation F).map_add x y) with hx | hy
  · exact le_max_of_le_left (NNReal.coe_le_coe.mpr (h hx))
  · exact le_max_of_le_right (NNReal.coe_le_coe.mpr (h hy))

@[simp] theorem residueNormalizedAbsoluteValue_uniformizer :
    residueNormalizedAbsoluteValue F (uniformizer F) = (residueCardinality F : ℝ) ^ (-1 : ℤ) :=
  residueNormalizedAbsoluteValue_of_ord_eq F (ord_uniformizer F)

/-- Every order-one choice has the same normalized absolute value. -/
theorem residueNormalizedAbsoluteValue_of_ord_one {π : F} (hπ : FML.ord F π = 1) :
    residueNormalizedAbsoluteValue F π = (residueCardinality F : ℝ)⁻¹ := by
  simpa using residueNormalizedAbsoluteValue_of_ord_eq F hπ

/-- Valuation units have absolute value one. -/
theorem residueNormalizedAbsoluteValue_unit (x : Fˣ) (hx : x ∈ FML.unitGroup F) :
    residueNormalizedAbsoluteValue F (x : F) = 1 := by
  simpa using residueNormalizedAbsoluteValue_of_ord_eq F (FML.ord_unitGroup F x hx)

end Langlands.LocalField
