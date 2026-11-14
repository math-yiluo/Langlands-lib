import Langlands.Representation.GodementJacquet.UniformWhittakerSliceBound
import Langlands.AllField.Representation.GodementJacquet.WhittakerSliceBound
/-!
# Uniform exponents for unipotent slices

Choose the exponent using one fixed integral matrix box. Scalar dilation then
bounds every compact matrix support with this same exponent. The paired Markdown
records the construction and the resulting bound for Schwartz--Bruhat slices.
-/

noncomputable section

namespace Langlands.AllField.GodementJacquet.WhittakerTorus.Padic
open Langlands.GodementJacquet.WhittakerTorus.Padic hiding boxTest boxTest_apply_of_le exists_slice_bound exists_uniform_slice_bound isClopen_normBox isCompact_normBox measurable_matrixIntegrand normBox sliceBoundBorelSpace sliceBoundLocalField sliceBoundMeasurableSpace sliceBoundTopology sliceBoundUnipotentBorelSpace sliceBoundUnipotentMeasurableSpace sliceBoundValuativeRel sliceExponents torusMonomial torusMonomial_nonneg uniformSliceLocalField uniformSliceTopology uniformSliceUnipotentBorelSpace uniformSliceUnipotentMeasurableSpace uniformSliceValuativeRel unipotent_volume_bound_uniform
open Langlands.AllField.GodementJacquet.WhittakerTorus.Padic
open Langlands.GodementJacquet.WhittakerTorus
open Langlands.AllField.GodementJacquet.WhittakerTorus
open Langlands.GodementJacquet
open Langlands.AllField.GodementJacquet

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement diagonalConj_map normalizedAbsoluteValue normalizedAbsoluteValue_apply singleton_modulus_real unipotentHaar_mul_diagonal_le unipotentVolumeLocalField unipotentVolumeTopology unipotentVolumeValuativeRel
open Langlands.AllField.RankinSelberg
open Langlands.Whittaker
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear
open scoped BigOperators ENNReal

universe uF

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance uniformSliceUnipotentMeasurableSpace (n : ℕ) :
    MeasurableSpace (upperUnipotent (n + 1) F) := borel _
local instance uniformSliceUnipotentBorelSpace (n : ℕ) :
    BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩

private def unitMatrixBox (n : ℕ) :
    Set (Matrix (Fin (n + 1)) (Fin (n + 1)) F) :=
  Set.univ.pi fun _ => Set.univ.pi fun _ =>
    {x : F | (⟨⟩ : LocalFieldData F).normalizedAbs x ≤ 1}

private theorem isCompact_unitMatrixBox (n : ℕ) : IsCompact (unitMatrixBox F n) :=
  isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
    Langlands.AllField.Whittaker.JPSDilationAssembly.isCompact_le (⟨⟩ : LocalFieldData F) 1

/-- An exponent chosen from the unipotent-volume bound for the fixed integral
matrix box. It depends on the field and rank, before every test or translate. -/
def sliceExponents (n : ℕ) : Fin (n + 1) → ℕ :=
  (unipotentHaar_mul_diagonal_le n (unitMatrixBox F n)
    (isCompact_unitMatrixBox F n)).choose_spec.choose_spec.choose

/-- The same exponents bound the volume for every compact matrix support.
Only the cutoff unit and multiplicative constant depend on that support. -/
theorem unipotent_volume_bound_uniform (n : ℕ)
    (L : Set (Matrix (Fin (n + 1)) (Fin (n + 1)) F)) (hL : IsCompact L) :
    ∃ (r : Fˣ) (C : ℝ), ∀ a : Fin (n + 1) → Fˣ,
      ((∃ u : upperUnipotent (n + 1) F,
          u.val.val * Matrix.diagonal (fun i => (a i : F)) ∈ L) →
        ∀ i, (⟨⟩ : LocalFieldData F).normalizedAbs (a i : F) ≤
          (⟨⟩ : LocalFieldData F).normalizedAbs (r : F)) ∧
      unipotentHaar F n
          {u | u.val.val * Matrix.diagonal (fun i => (a i : F)) ∈ L} ≤
        ENNReal.ofReal (C * torusMonomial F (sliceExponents F n) a) := by
  set T := (⟨⟩ : LocalFieldData F)
  have hcont : Continuous fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) F =>
      ∑ i, ∑ j, T.normalizedAbs (M i j) :=
    continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      T.continuous_normalizedAbs.comp (continuous_id.matrix_elem i j)
  obtain ⟨R, hR⟩ := hL.bddAbove_image hcont.continuousOn
  have hentry : ∀ M ∈ L, ∀ i j, T.normalizedAbs (M i j) ≤ R := by
    intro M hM i j
    refine le_trans ?_ (hR ⟨M, hM, rfl⟩)
    refine le_trans ?_ (Finset.single_le_sum (fun i _ => Finset.sum_nonneg fun j _ =>
      T.normalizedAbs_nonneg (M i j)) (Finset.mem_univ i))
    exact Finset.single_le_sum (fun j _ => T.normalizedAbs_nonneg (M i j)) (Finset.mem_univ j)
  have hq : (1 : ℝ) < T.residueCardinality := Nat.one_lt_cast.mpr T.residueCardinality_gt_one
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt R hq
  let r : Fˣ := Langlands.LocalFactor.LocalAbelian.uniformizerUnit T ^ (-(m : ℤ))
  set ρ := T.normalizedAbs (r : F) with hρdef
  have hρ : ρ = (T.residueCardinality : ℝ) ^ m := by
    rw [hρdef, Langlands.LocalFactor.LocalAbelian.uniformizerUnit_zpow_abs, neg_neg, zpow_natCast]
  have hρpos : 0 < ρ := T.normalizedAbs_pos r.ne_zero
  have hRρ : R ≤ ρ := hρ ▸ hm.le
  let C₀ : ℝ := (unipotentHaar_mul_diagonal_le n (unitMatrixBox F n)
    (isCompact_unitMatrixBox F n)).choose_spec.choose
  have hfixed := (unipotentHaar_mul_diagonal_le n (unitMatrixBox F n)
    (isCompact_unitMatrixBox F n)).choose_spec.choose_spec.choose_spec
  refine ⟨r, C₀ * ∏ i, ρ ^ sliceExponents F n i, fun a => ?_⟩
  refine ⟨?_, ?_⟩
  · rintro ⟨u, hu⟩ i
    have hh := hentry _ hu i i
    rw [Matrix.mul_diagonal,
      show u.val.val i i = 1 from UpperUnipotent.entry_diag u i, one_mul] at hh
    exact hh.trans hRρ
  · let b : Fin (n + 1) → Fˣ := fun i => a i * r⁻¹
    have hsub : {u : upperUnipotent (n + 1) F |
        u.val.val * Matrix.diagonal (fun i => (a i : F)) ∈ L} ⊆
        {u | u.val.val * Matrix.diagonal (fun i => (b i : F)) ∈ unitMatrixBox F n} := by
      intro u hu i _ j _
      change T.normalizedAbs
        ((u.val.val * Matrix.diagonal (fun i => (b i : F))) i j) ≤ 1
      have hh := (hentry _ hu i j).trans hRρ
      rw [Matrix.mul_diagonal] at hh
      rw [Matrix.mul_diagonal]
      change T.normalizedAbs (u.val.val i j * ((a j * r⁻¹ : Fˣ) : F)) ≤ 1
      rw [Units.val_mul, ← mul_assoc, T.normalizedAbs_mul,
        Langlands.AllField.Whittaker.JPSDilationAssembly.normalizedAbs_units_inv]
      exact mul_inv_le_one_of_le₀ hh hρpos.le
    have hmono : torusMonomial F (sliceExponents F n) b =
        (∏ i, ρ ^ sliceExponents F n i) * torusMonomial F (sliceExponents F n) a := by
      change (∏ i, (T.normalizedAbs (b i : F))⁻¹ ^ sliceExponents F n i) =
        (∏ i, ρ ^ sliceExponents F n i) *
          ∏ i, (T.normalizedAbs (a i : F))⁻¹ ^ sliceExponents F n i
      simp only [b, Units.val_mul, T.normalizedAbs_mul,
        Langlands.AllField.Whittaker.JPSDilationAssembly.normalizedAbs_units_inv, mul_inv, inv_inv, mul_pow,
        Finset.prod_mul_distrib]
      ring
    calc unipotentHaar F n
          {u | u.val.val * Matrix.diagonal (fun i => (a i : F)) ∈ L}
        ≤ unipotentHaar F n
          {u | u.val.val * Matrix.diagonal (fun i => (b i : F)) ∈ unitMatrixBox F n} :=
            measure_mono hsub
      _ ≤ ENNReal.ofReal (C₀ * torusMonomial F (sliceExponents F n) b) := (hfixed b).2
      _ = ENNReal.ofReal ((C₀ * ∏ i, ρ ^ sliceExponents F n i) *
          torusMonomial F (sliceExponents F n) a) := by rw [hmono, mul_assoc]

/-- Uniform slice bound: the exponents are fixed before both the full-matrix
Schwartz--Bruhat test and its right translate. -/
theorem exists_uniform_slice_bound {n : ℕ} (Φ : MatrixTestFunction n F)
    (k : Langlands.GeneralLinear (n + 1) F) :
    ∃ (B : ℝ) (ρ : ℝ) (hρ : 0 < ρ), ∀ a : Fin (n + 1) → Fˣ,
      ∫⁻ u, ‖Φ (u.val.val * Matrix.diagonal (fun i => (a i : F)) * k.val)‖ₑ
          ∂unipotentHaar F n ≤
        ENNReal.ofReal B * ENNReal.ofReal (torusMonomial F (sliceExponents F n) a) *
          ‖boxTest F n hρ (fun i => (a i : F))‖ₑ := by
  obtain ⟨B, hB⟩ := Φ.continuous.bounded_above_of_compact_support Φ.hasCompactSupport
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  let L : Set (Matrix (Fin (n + 1)) (Fin (n + 1)) F) :=
    (fun M => M * (k⁻¹ : Langlands.GeneralLinear (n + 1) F).val) ''
      tsupport (Φ : Matrix (Fin (n + 1)) (Fin (n + 1)) F → ℂ)
  have hL : IsCompact L :=
    Φ.hasCompactSupport.isCompact.image (continuous_id.matrix_mul continuous_const)
  obtain ⟨r, C, hvol⟩ := unipotent_volume_bound_uniform F n L hL
  have hρ : 0 < (⟨⟩ : LocalFieldData F).normalizedAbs (r : F) :=
    (⟨⟩ : LocalFieldData F).normalizedAbs_pos r.ne_zero
  refine ⟨B * |C|, _, hρ, fun a => ?_⟩
  let E : Set (upperUnipotent (n + 1) F) :=
    {u | u.val.val * Matrix.diagonal (fun i => (a i : F)) ∈ L}
  have hpt : ∀ u : upperUnipotent (n + 1) F,
      ‖Φ (u.val.val * Matrix.diagonal (fun i => (a i : F)) * k.val)‖ₑ ≤
        E.indicator (fun _ => ENNReal.ofReal B) u := by
    intro u
    by_cases hu : u ∈ E
    · rw [Set.indicator_of_mem hu, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hB _)
    · have hnot : u.val.val * Matrix.diagonal (fun i => (a i : F)) * k.val ∉
          tsupport (Φ : Matrix (Fin (n + 1)) (Fin (n + 1)) F → ℂ) := by
        intro h
        refine hu ⟨_, h, ?_⟩
        change u.val.val * Matrix.diagonal (fun i => (a i : F)) * k.val *
            (k⁻¹ : Langlands.GeneralLinear (n + 1) F).val =
          u.val.val * Matrix.diagonal (fun i => (a i : F))
        rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
      rw [image_eq_zero_of_notMem_tsupport hnot, enorm_zero]
      exact zero_le
  have hM : 0 ≤ torusMonomial F (sliceExponents F n) a := torusMonomial_nonneg F (sliceExponents F n) a
  calc ∫⁻ u, ‖Φ (u.val.val * Matrix.diagonal (fun i => (a i : F)) * k.val)‖ₑ
        ∂unipotentHaar F n
      ≤ ∫⁻ u, E.indicator (fun _ => ENNReal.ofReal B) u ∂unipotentHaar F n :=
        lintegral_mono hpt
    _ ≤ ENNReal.ofReal B * unipotentHaar F n E := lintegral_indicator_const_le E _
    _ ≤ ENNReal.ofReal (B * |C|) * ENNReal.ofReal (torusMonomial F (sliceExponents F n) a) *
          ‖boxTest F n hρ (fun i => (a i : F))‖ₑ := by
      by_cases hbox : ∀ i, (⟨⟩ : LocalFieldData F).normalizedAbs (a i : F) ≤
          (⟨⟩ : LocalFieldData F).normalizedAbs (r : F)
      · rw [boxTest_apply_of_le F hρ hbox, enorm_one, mul_one,
          ENNReal.ofReal_mul hB0, mul_assoc]
        gcongr
        refine (hvol a).2.trans ?_
        rw [← ENNReal.ofReal_mul (abs_nonneg C)]
        exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_abs_self C) hM)
      · have hE : E = ∅ :=
          Set.eq_empty_iff_forall_notMem.2 fun u hu => hbox ((hvol a).1 ⟨u, hu⟩)
        rw [hE, measure_empty, mul_zero]
        exact zero_le

end Langlands.AllField.GodementJacquet.WhittakerTorus.Padic
