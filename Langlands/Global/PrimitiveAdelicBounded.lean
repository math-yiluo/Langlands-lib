import Langlands.Global.PrimitiveAdelicNormalization
import Langlands.Global.PositiveRealIdeles
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-! # Compact representatives for bounded primitive adelic heights -/

noncomputable section

universe u

open scoped NNReal Topology Matrix

namespace Langlands.Global.PrimitiveAdelicHeight

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

/-- The positive scalar adele extended to all real parameters, with finite part
one. At parameter zero it is an adele, rather than an idele. -/
def realScalarAdele (r : ℝ) : Adeles F :=
  (PositiveRealIdeles.infiniteRealEmbedding F r, 1)

theorem continuous_realScalarAdele : Continuous (realScalarAdele F) :=
  (PositiveRealIdeles.continuous_infiniteRealEmbedding F).prodMk continuous_const

@[simp] theorem realScalarAdele_coe (r : ℝ≥0ˣ) :
    realScalarAdele F ((r : ℝ≥0) : ℝ) = (PositiveRealIdeles.full F r).val := rfl

/-- The positive root that splits off the normalized absolute value of an idele. -/
def scalarRoot (h : ℝ≥0ˣ) : ℝ≥0ˣ :=
  Units.map (NNReal.rpowMonoidHom ((Module.finrank ℚ F : ℝ)⁻¹)) h

@[simp] theorem scalarRoot_pow (h : ℝ≥0ˣ) :
    scalarRoot F h ^ Module.finrank ℚ F = h := by
  apply Units.ext
  exact NNReal.rpow_inv_natCast_pow _ Module.finrank_pos.ne'

@[simp] theorem absoluteValue_scalarRoot (h : ℝ≥0ˣ) :
    IdeleAbsoluteValue.full F (PositiveRealIdeles.full F (scalarRoot F h)) = h := by
  rw [PositiveRealIdeles.absoluteValue_full, scalarRoot_pow]

theorem scalarRoot_le (h : ℝ≥0ˣ) (R : ℝ) (hR : ((h : ℝ≥0) : ℝ) ≤ R) :
    ((scalarRoot F h : ℝ≥0) : ℝ) ≤ max 1 R := by
  let r : ℝ := ((scalarRoot F h : ℝ≥0) : ℝ)
  by_cases hr : r ≤ 1
  · exact hr.trans (le_max_left _ _)
  · have hp : r ^ Module.finrank ℚ F = ((h : ℝ≥0) : ℝ) :=
      congrArg (fun z : ℝ≥0ˣ => ((z : ℝ≥0) : ℝ)) (scalarRoot_pow F h)
    exact ((le_self_pow₀ (le_of_not_ge hr) Module.finrank_pos.ne').trans
      (hp.le.trans hR)).trans (le_max_right _ _)

/-- A compact candidate set for rational-scalar representatives of height at
most `R`, formed from a norm-one idele set and the fixed normalized vector set. -/
def boundedRepresentativeSet (C : Set (Ideles F)) (R : ℝ) : Set (Vector F n) :=
  (fun p : ℝ × Ideles F × Vector F n =>
    realScalarAdele F p.1 • (p.2.1.val • p.2.2)) ''
      (Set.Icc 0 (max 1 R) ×ˢ (C ×ˢ normalizedSet F n))

theorem isCompact_boundedRepresentativeSet (C : Set (Ideles F)) (hC : IsCompact C)
    (R : ℝ) : IsCompact (boundedRepresentativeSet F n C R) := by
  apply (isCompact_Icc.prod (hC.prod (isCompact_normalizedSet F n))).image
  exact ((continuous_realScalarAdele F).comp continuous_fst).smul
    ((Units.continuous_val.comp (continuous_fst.comp continuous_snd)).smul
      (continuous_snd.comp continuous_snd))

/-- Every primitive vector of bounded height has a principal scalar multiple
in the compact representative set built from any norm-one fundamental set. -/
theorem exists_diagonal_smul_mem_boundedRepresentativeSet
    (C : Set (Ideles F))
    (hcover : ∀ z ∈ NormOneIdeleClass.normOneIdeles F,
      ∃ a : Fˣ, diagonalUnits F a * z ∈ C)
    (R : ℝ) (x : Vector F n) (hx : IsPrimitive F n x) (hR : height F n x ≤ R) :
    ∃ a : Fˣ, (diagonalUnits F a).val • x ∈ boundedRepresentativeSet F n C R := by
  obtain ⟨t, y, hy, hxy, ht⟩ := exists_content_mul_normalized F n x hx
  let r := scalarRoot F (positiveHeight F n x hx)
  let s := PositiveRealIdeles.full F r
  have hs : IdeleAbsoluteValue.full F s = positiveHeight F n x hx :=
    absoluteValue_scalarRoot F _
  have hz : s⁻¹ * t ∈ NormOneIdeleClass.normOneIdeles F := by
    change IdeleAbsoluteValue.full F (s⁻¹ * t) = 1
    rw [map_mul, map_inv, hs, ht, inv_mul_cancel]
  obtain ⟨a, ha⟩ := hcover (s⁻¹ * t) hz
  refine ⟨a, ⟨(((r : ℝ≥0) : ℝ), diagonalUnits F a * (s⁻¹ * t), y),
    ⟨⟨NNReal.coe_nonneg _, scalarRoot_le F _ R hR⟩, ha, hy⟩, ?_⟩⟩
  change realScalarAdele F ((r : ℝ≥0) : ℝ) •
    ((diagonalUnits F a * (s⁻¹ * t)).val • y) = (diagonalUnits F a).val • x
  rw [realScalarAdele_coe, smul_smul, ← Units.val_mul, hxy, smul_smul,
    ← Units.val_mul]
  congr 1
  apply congrArg Units.val
  change s * (diagonalUnits F a * (s⁻¹ * t)) = diagonalUnits F a * t
  rw [mul_left_comm s, mul_inv_cancel_left]

/-- There is one compact set meeting every principal-scalar class of primitive
vectors with height at most the prescribed real bound. -/
theorem exists_isCompact_bounded_representatives (R : ℝ) :
    ∃ B : Set (Vector F n), IsCompact B ∧
      ∀ x : Vector F n, IsPrimitive F n x → height F n x ≤ R →
        ∃ a : Fˣ, (diagonalUnits F a).val • x ∈ B := by
  obtain ⟨C, hC, _, hcover⟩ := NormOneIdeleClass.exists_isCompact_fundamentalSet F
  exact ⟨boundedRepresentativeSet F n C R, isCompact_boundedRepresentativeSet F n C hC R,
    fun x hx hR => exists_diagonal_smul_mem_boundedRepresentativeSet F n C hcover R x hx hR⟩

end Langlands.Global.PrimitiveAdelicHeight
