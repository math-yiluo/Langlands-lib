import Langlands.LocalField.LocalFieldData

/-! # Arithmetic laws for supplied nonarchimedean local-field data -/

namespace Langlands.LocalFieldData

open scoped WithZero
universe u
variable {F : Type u} [Field F] (T : LocalFieldData F)

theorem finite_residueField : Finite T.ResidueField := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  exact inferInstanceAs (Finite (IsLocalRing.ResidueField
    (ValuativeRel.valuation F).integer))

theorem residueCardinality_gt_one : 1 < T.residueCardinality := by
  let := T.finite_residueField
  let := Fintype.ofFinite T.ResidueField
  simpa [residueCardinality, Nat.card_eq_fintype_card] using
    (Fintype.one_lt_card : 1 < Fintype.card T.ResidueField)


theorem discreteValuation_surjective : Function.Surjective T.discreteValuation := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  exact (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F).surjective.comp
    ValuativeRel.valuation_surjective

theorem discreteValuation_uniformizer :
    T.discreteValuation T.uniformizer = WithZero.exp (-1) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F
  have h : ValuativeRel.valuation F T.uniformizer =
      e.symm (WithZero.exp (-1)) :=
    (ValuativeRel.valuation_surjective (e.symm (WithZero.exp (-1)))).choose_spec
  change e (ValuativeRel.valuation F T.uniformizer) = WithZero.exp (-1)
  rw [h, e.apply_symm_apply]

theorem ord_zero : T.ord 0 = 0 := by simp [ord]

theorem ord_one : T.ord 1 = 0 := by simp [ord]

theorem ord_uniformizer : T.ord T.uniformizer = 1 := by
  simp [ord, T.discreteValuation_uniformizer]

theorem ord_mul {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) :
    T.ord (x * y) = T.ord x + T.ord y := by
  simp [ord, map_mul, WithZero.log_mul
    ((T.discreteValuation.ne_zero_iff).mpr hx)
    ((T.discreteValuation.ne_zero_iff).mpr hy), add_comm]

theorem ord_inv (x : F) : T.ord x⁻¹ = -T.ord x := by
  simp [ord, map_inv₀, WithZero.log_inv]

theorem min_ord_le_ord_add {x y : F} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : x + y ≠ 0) : min (T.ord x) (T.ord y) ≤ T.ord (x + y) := by
  change min (-WithZero.log (T.discreteValuation x)) (-WithZero.log (T.discreteValuation y)) ≤
    -WithZero.log (T.discreteValuation (x + y))
  rcases le_max_iff.mp (T.discreteValuation.map_add x y) with h | h
  · exact (min_le_left _ _).trans (neg_le_neg ((WithZero.log_le_log
      (T.discreteValuation.ne_zero_iff.mpr hxy) (T.discreteValuation.ne_zero_iff.mpr hx)).mpr h))
  · exact (min_le_right _ _).trans (neg_le_neg ((WithZero.log_le_log
      (T.discreteValuation.ne_zero_iff.mpr hxy) (T.discreteValuation.ne_zero_iff.mpr hy)).mpr h))

theorem ord_surjective_nonzero (n : ℤ) : ∃ x : F, x ≠ 0 ∧ T.ord x = n := by
  obtain ⟨x, hx⟩ := T.discreteValuation_surjective (WithZero.exp (-n))
  refine ⟨x, ?_, ?_⟩
  · intro h
    exact WithZero.exp_ne_zero (by rw [← hx, h, map_zero])
  · simp [ord, hx]


theorem normalizedAbs_zero : T.normalizedAbs 0 = 0 := by simp [normalizedAbs]

theorem normalizedAbs_one : T.normalizedAbs 1 = 1 := by
  simp [normalizedAbs, T.ord_one]

theorem normalizedAbs_of_ne_zero {x : F} (hx : x ≠ 0) :
    T.normalizedAbs x = (T.residueCardinality : ℝ) ^ (-T.ord x) := by
  simp [normalizedAbs, hx]

theorem normalizedAbs_pos {x : F} (hx : x ≠ 0) : 0 < T.normalizedAbs x := by
  rw [T.normalizedAbs_of_ne_zero hx]
  exact zpow_pos (by exact_mod_cast (lt_trans Nat.zero_lt_one T.residueCardinality_gt_one)) _

theorem normalizedAbs_nonneg (x : F) : 0 ≤ T.normalizedAbs x := by
  by_cases hx : x = 0
  · simp [hx, T.normalizedAbs_zero]
  exact (T.normalizedAbs_pos hx).le

theorem normalizedAbs_le_iff_of_ne_zero {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) :
    T.normalizedAbs x ≤ T.normalizedAbs y ↔
      T.discreteValuation x ≤ T.discreteValuation y := by
  rw [T.normalizedAbs_of_ne_zero hx, T.normalizedAbs_of_ne_zero hy]
  simp only [ord, neg_neg]
  rw [zpow_le_zpow_iff_right₀ (by exact_mod_cast T.residueCardinality_gt_one)]
  exact WithZero.log_le_log ((T.discreteValuation.ne_zero_iff).mpr hx)
    ((T.discreteValuation.ne_zero_iff).mpr hy)

theorem normalizedAbs_mul (x y : F) :
    T.normalizedAbs (x * y) = T.normalizedAbs x * T.normalizedAbs y := by
  by_cases hx : x = 0
  · simp [hx, T.normalizedAbs_zero]
  by_cases hy : y = 0
  · simp [hy, T.normalizedAbs_zero]
  rw [T.normalizedAbs_of_ne_zero (mul_ne_zero hx hy),
    T.normalizedAbs_of_ne_zero hx, T.normalizedAbs_of_ne_zero hy,
    T.ord_mul hx hy, neg_add, zpow_add₀]
  exact_mod_cast (lt_trans Nat.zero_lt_one T.residueCardinality_gt_one).ne'

theorem normalizedAbs_add_le_max (x y : F) :
    T.normalizedAbs (x + y) ≤ max (T.normalizedAbs x) (T.normalizedAbs y) := by
  by_cases hx : x = 0
  · simp [hx, T.normalizedAbs_zero]
  by_cases hy : y = 0
  · simp [hy, T.normalizedAbs_zero]
  by_cases hxy : x + y = 0
  · rw [hxy, T.normalizedAbs_zero]
    exact le_trans (T.normalizedAbs_nonneg x) (le_max_left _ _)
  rcases le_max_iff.mp (T.discreteValuation.map_add x y) with h | h
  · exact le_max_of_le_left ((T.normalizedAbs_le_iff_of_ne_zero hxy hx).mpr h)
  · exact le_max_of_le_right ((T.normalizedAbs_le_iff_of_ne_zero hxy hy).mpr h)

theorem normalizedAbs_uniformizer :
    T.normalizedAbs T.uniformizer = (T.residueCardinality : ℝ) ^ (-1 : ℤ) := by
  have hπ : T.uniformizer ≠ 0 := by
    intro h
    have ho := T.ord_uniformizer
    rw [h, T.ord_zero] at ho
    exact zero_ne_one ho
  rw [T.normalizedAbs_of_ne_zero hπ, T.ord_uniformizer]


theorem ord_zpow (x : F) (n : ℤ) : T.ord (x ^ n) = n * T.ord x := by
  simp [ord, map_zpow₀, WithZero.log_zpow, mul_neg]


end Langlands.LocalFieldData
