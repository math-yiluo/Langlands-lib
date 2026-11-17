import Langlands.Global.AdelicGLCompactIwasawa
import Langlands.Global.RankinSelberg.AdelicGaugeLastRowMajorant
import Langlands.Global.RankinSelberg.AdelicSimpleRootGauge
import Langlands.Global.RankinSelberg.UnfoldingWhittaker

/-! # Schwartz bounds for compact right translates of a simple-root gauge -/

noncomputable section
universe u
open NumberField Set
open scoped Classical CategoryTheory.MonObj ENNReal NNReal
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

open Langlands.Global PrimitiveAdelicHeight

local instance gaugeTranslateSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _

variable (F : Type u) [Field F] [NumberField F]

private theorem diagonalMatrixUnits_eq_diagonalGL (n : ℕ) (d : Fin n → Ideles F) :
    GroupScheme.GeneralLinear.diagonalMatrixUnits (Adeles F) d = diagonalGL d :=
  Units.ext rfl

theorem gaugeDiagonalPoint_mul (n : ℕ) (d e : Fin n → Ideles F) :
    gaugeDiagonalPoint F n (d * e) =
      gaugeDiagonalPoint F n d * gaugeDiagonalPoint F n e := by
  simp only [gaugeDiagonalPoint, map_mul]

theorem gaugeDiagonalPoint_conj_mem_unipotent (n : ℕ) (d : Fin n → Ideles F)
    (u : unipotentAdelic F n) :
    gaugeDiagonalPoint F n d * (u : Points F n) * (gaugeDiagonalPoint F n d)⁻¹ ∈
      unipotentAdelic F n := by
  rw [Unfolding.mem_unipotentAdelic_iff]
  simp only [map_mul, map_inv, gaugeDiagonalPoint, MulEquiv.apply_symm_apply,
    diagonalMatrixUnits_eq_diagonalGL, Units.val_mul]
  change IsUnitriangular
    (Matrix.diagonal (fun i => (d i : Adeles F)) *
      (GeneralLinearGroupPoints.adelicEquiv F n u :
        Matrix (Fin n) (Fin n) (Adeles F)) *
      Matrix.diagonal (fun i => (((d i)⁻¹ : Ideles F) : Adeles F)))
  exact (Unfolding.isUnitriangular_of_mem_unipotentAdelic F u).diagonal_conj d

/-- Compact sets of actual adelic points have Iwasawa factorizations with
diagonal idele tuples in one compact set. -/
theorem exists_compact_gaugeDiagonal_parameters (n : ℕ)
    {C : Set (Points F n)} (hC : IsCompact C) :
    ∃ D : Set (Fin n → Ideles F), IsCompact D ∧
      ∀ c ∈ C, ∃ e ∈ D, ∃ u : unipotentAdelic F n,
        ∃ k : gaugeStandardCompact F n,
          c = (u : Points F n) * gaugeDiagonalPoint F n e * (k : Points F n) := by
  let E := GeneralLinearGroupPoints.adelicHomeomorph F n
  obtain ⟨D, hD, hfac⟩ := exists_compact_iwasawaDiagonal F n (hC.image E.continuous)
  refine ⟨D, hD, fun c hc => ?_⟩
  obtain ⟨e, he, u, k, hu, hk, h⟩ := hfac (E c) (mem_image_of_mem E hc)
  have hu' : (GeneralLinearGroupPoints.adelicEquiv F n).symm u ∈
      unipotentAdelic F n := by
    rw [Unfolding.mem_unipotentAdelic_iff, MulEquiv.apply_symm_apply]
    exact hu
  have hk' : (GeneralLinearGroupPoints.adelicEquiv F n).symm k ∈
      gaugeStandardCompact F n := by
    change GeneralLinearGroupPoints.adelicEquiv F n
      ((GeneralLinearGroupPoints.adelicEquiv F n).symm k) ∈ standardCompact F n
    simpa only [MulEquiv.apply_symm_apply] using hk
  refine ⟨e, he, ⟨_, hu'⟩, ⟨_, hk'⟩, ?_⟩
  apply (GeneralLinearGroupPoints.adelicEquiv F n).injective
  change E c = _
  simpa only [map_mul, gaugeDiagonalPoint, MulEquiv.apply_symm_apply,
    diagonalMatrixUnits_eq_diagonalGL] using h

theorem gauge_diagonal_mul_iwasawa (r : ℕ) {τ : ℝ}
    {Ξ : Points F (r + 1) → ℝ≥0∞} (hΞ : IsAdelicSimpleRootGauge F r τ Ξ)
    (d e : Fin (r + 1) → Ideles F) (u : unipotentAdelic F (r + 1))
    (k : gaugeStandardCompact F (r + 1)) :
    Ξ (gaugeDiagonalPoint F (r + 1) d *
      ((u : Points F (r + 1)) * gaugeDiagonalPoint F (r + 1) e *
        (k : Points F (r + 1)))) =
      Ξ (gaugeDiagonalPoint F (r + 1) (d * e)) := by
  let v : unipotentAdelic F (r + 1) :=
    ⟨_, gaugeDiagonalPoint_conj_mem_unipotent F (r + 1) d u⟩
  have h : gaugeDiagonalPoint F (r + 1) d *
      ((u : Points F (r + 1)) * gaugeDiagonalPoint F (r + 1) e *
        (k : Points F (r + 1))) =
      (v : Points F (r + 1)) *
        (gaugeDiagonalPoint F (r + 1) (d * e) * (k : Points F (r + 1))) := by
    rw [gaugeDiagonalPoint_mul]
    dsimp only [v]
    group
  rw [h, hΞ.2.2.1, hΞ.2.2.2.1]

/-- Right multiplication of the simple-root row by this diagonal matrix
multiplies the diagonal idele tuple by the given parameter. -/
def gaugeRootTranslateMatrix (r : ℕ) (e : Fin (r + 1) → Ideles F) : AdelicGL F r :=
  diagonalGL (gaugeSimpleRootIdeles F r e)

theorem continuous_gaugeRootTranslateMatrix (r : ℕ) :
    Continuous (gaugeRootTranslateMatrix F r) := by
  have h (i : Fin r) : Continuous fun e : Fin (r + 1) → Ideles F =>
      gaugeSimpleRootIdeles F r e i :=
    (continuous_apply i.castSucc).div' (continuous_apply i.succ)
  apply Units.continuous_iff.mpr
  constructor
  · change Continuous fun e => Matrix.diagonal
      (fun i => (gaugeSimpleRootIdeles F r e i : Adeles F))
    exact continuous_matrix fun i j => by
      by_cases hij : i = j
      · subst j
        simpa only [Matrix.diagonal_apply, ite_true, Function.comp_def] using
          Units.continuous_val.comp (h i)
      · simpa only [Matrix.diagonal_apply,
          ite_eq_right hij] using (continuous_const : Continuous fun _ :
            Fin (r + 1) → Ideles F => (0 : Adeles F))
  · change Continuous fun e => Matrix.diagonal
      (fun i => (((gaugeSimpleRootIdeles F r e i)⁻¹ : Ideles F) : Adeles F))
    exact continuous_matrix fun i j => by
      by_cases hij : i = j
      · subst j
        simpa only [Matrix.diagonal_apply, ite_true, Function.comp_def] using
          Units.continuous_coe_inv.comp (h i)
      · simpa only [Matrix.diagonal_apply,
          ite_eq_right hij] using (continuous_const : Continuous fun _ :
            Fin (r + 1) → Ideles F => (0 : Adeles F))

theorem gaugeSimpleRootRow_mul (r : ℕ) (d e : Fin (r + 1) → Ideles F) :
    gaugeSimpleRootRow F r (d * e) =
      gaugeSimpleRootRow F r d *
        (gaugeRootTranslateMatrix F r e : Matrix (Fin r) (Fin r) (Adeles F)) := by
  ext i j
  simp only [gaugeRootTranslateMatrix, diagonalGL, Matrix.mul_diagonal,
    gaugeSimpleRootRow, gaugeSimpleRootIdeles, Pi.mul_apply]
  rw [← Units.val_mul]
  congr 1
  simp only [div_eq_mul_inv, mul_inv_rev]
  ac_rfl

theorem gaugeSimpleRootNormProduct_pos (r : ℕ) (d : Fin (r + 1) → Ideles F) :
    0 < gaugeSimpleRootNormProduct F r d :=
  Finset.prod_pos fun _ _ => IdeleAbsoluteValue.full_pos F _

theorem continuous_gaugeSimpleRootNormProduct (r : ℕ) :
    Continuous (gaugeSimpleRootNormProduct F r) := by
  apply continuous_finsetProd
  intro i _
  exact NNReal.continuous_coe.comp (Units.continuous_val.comp
    ((IdeleAbsoluteValue.full F).continuous.comp
      ((continuous_apply i.castSucc).div' (continuous_apply i.succ))))

theorem gaugeSimpleRootNormProduct_mul (r : ℕ)
    (d e : Fin (r + 1) → Ideles F) :
    gaugeSimpleRootNormProduct F r (d * e) =
      gaugeSimpleRootNormProduct F r d * gaugeSimpleRootNormProduct F r e := by
  have hroot (i : Fin r) : gaugeSimpleRootIdeles F r (d * e) i =
      gaugeSimpleRootIdeles F r d i * gaugeSimpleRootIdeles F r e i := by
    simp only [gaugeSimpleRootIdeles, Pi.mul_apply, div_eq_mul_inv, mul_inv_rev]
    ac_rfl
  simp only [gaugeSimpleRootNormProduct, hroot, map_mul, Units.val_mul,
    NNReal.coe_mul, Finset.prod_mul_distrib]

/-- A compact set of right translates admits a single Schwartz bound on the
simple-root row, with the original gauge exponent. -/
theorem exists_compact_gaugeDiagonal_translate_majorant
    [CompactSpace (AdeleQuotient F)] (r : ℕ) {τ : ℝ}
    {Ξ : Points F (r + 1) → ℝ≥0∞} (hΞ : IsAdelicSimpleRootGauge F r τ Ξ)
    {C : Set (Points F (r + 1))} (hC : IsCompact C) :
    ∃ φ : RowVector F r → ℂ, φ ∈ schwartzBruhat F r ∧
      ∃ A : ℝ, 0 ≤ A ∧
        ∀ (d : Fin (r + 1) → Ideles F) (c : Points F (r + 1)), c ∈ C →
          Ξ (gaugeDiagonalPoint F (r + 1) d * c) ≤
            ENNReal.ofReal A *
              ENNReal.ofReal (gaugeSimpleRootNormProduct F r d ^ (-τ)) *
                ‖φ (gaugeSimpleRootRow F r d)‖ₑ := by
  obtain ⟨D, hD, hfac⟩ := exists_compact_gaugeDiagonal_parameters F (r + 1) hC
  obtain ⟨Φ, hΦ, hformula⟩ := hΞ.2.2.2.2
  obtain ⟨φ, hφ, hbound⟩ := exists_compact_row_majorant F r hΦ
    (hD.image (continuous_gaugeRootTranslateMatrix F r))
  have hpow : Continuous fun e : Fin (r + 1) → Ideles F =>
      gaugeSimpleRootNormProduct F r e ^ (-τ) :=
    (continuous_gaugeSimpleRootNormProduct F r).rpow_const fun e =>
      Or.inl (ne_of_gt (gaugeSimpleRootNormProduct_pos F r e))
  obtain ⟨B, hB⟩ := hD.bddAbove_image hpow.continuousOn
  refine ⟨φ, hφ, max B 0, le_max_right _ _, fun d c hc => ?_⟩
  obtain ⟨e, he, u, k, rfl⟩ := hfac c hc
  rw [gauge_diagonal_mul_iwasawa F r hΞ, hformula, gaugeSimpleRootNormProduct_mul,
    Real.mul_rpow (le_of_lt (gaugeSimpleRootNormProduct_pos F r d))
      (le_of_lt (gaugeSimpleRootNormProduct_pos F r e)),
    ENNReal.ofReal_mul (Real.rpow_nonneg
      (le_of_lt (gaugeSimpleRootNormProduct_pos F r d)) _),
    gaugeSimpleRootRow_mul]
  have heB : gaugeSimpleRootNormProduct F r e ^ (-τ) ≤ max B 0 :=
    (hB (mem_image_of_mem _ he)).trans (le_max_left _ _)
  have hrow : ‖Φ (gaugeSimpleRootRow F r d *
      (gaugeRootTranslateMatrix F r e :
        Matrix (Fin r) (Fin r) (Adeles F)))‖ₑ ≤
        ‖φ (gaugeSimpleRootRow F r d)‖ₑ := by
    simpa only [← ofReal_norm] using ENNReal.ofReal_le_ofReal
      (hbound (gaugeSimpleRootRow F r d) (gaugeRootTranslateMatrix F r e)
        (mem_image_of_mem _ he))
  calc
    _ ≤ (ENNReal.ofReal (gaugeSimpleRootNormProduct F r d ^ (-τ)) *
        ENNReal.ofReal (max B 0)) * ‖φ (gaugeSimpleRootRow F r d)‖ₑ :=
      mul_le_mul (mul_le_mul le_rfl (ENNReal.ofReal_le_ofReal heB) bot_le bot_le)
        hrow bot_le bot_le
    _ = _ := by rw [mul_comm (ENNReal.ofReal (max B 0))]

/-- The complete gauge--Schwartz kernel has a compact-uniform bound in the
simple-root variables and the last diagonal idele. -/
theorem exists_compact_gaugeSchwartz_kernel_majorant
    [CompactSpace (AdeleQuotient F)] (r : ℕ) {τ : ℝ}
    {Ξ : Points F (r + 1) → ℝ≥0∞} (hΞ : IsAdelicSimpleRootGauge F r τ Ξ)
    {Φ : RowVector F (r + 1) → ℂ} (hΦ : Φ ∈ schwartzBruhat F (r + 1))
    {C : Set (Points F (r + 1))} (hC : IsCompact C) (σ : ℝ) :
    ∃ φ : RowVector F r → ℂ, φ ∈ schwartzBruhat F r ∧
      ∃ ψ : RowVector F 1 → ℂ, ψ ∈ schwartzBruhat F 1 ∧
        ∃ A : ℝ, 0 ≤ A ∧
          ∀ (d : Fin (r + 1) → Ideles F) (c : Points F (r + 1)), c ∈ C →
            Ξ (gaugeDiagonalPoint F (r + 1) d * c) *
                ‖Φ (lastRow F r (gaugeDiagonalPoint F (r + 1) d * c))‖ₑ *
                ENNReal.ofReal (detNorm F (r + 1)
                  (gaugeDiagonalPoint F (r + 1) d * c) ^ σ) ≤
              ENNReal.ofReal A *
                ENNReal.ofReal (gaugeSimpleRootNormProduct F r d ^ (-τ)) *
                ‖φ (gaugeSimpleRootRow F r d)‖ₑ *
                ‖ψ (singleRow F (d (Fin.last r) : Adeles F))‖ₑ *
                ENNReal.ofReal
                  (detNorm F (r + 1) (gaugeDiagonalPoint F (r + 1) d) ^ σ) := by
  obtain ⟨φ, hφ, A, hA, hΞbound⟩ :=
    exists_compact_gaugeDiagonal_translate_majorant F r hΞ hC
  obtain ⟨ψ, hψ, hΦbound⟩ :=
    exists_compact_gaugeDiagonal_lastRow_majorant F r hΦ hC
  have hdet : Continuous fun c : Points F (r + 1) => detNorm F (r + 1) c ^ σ :=
    (Unfolding.continuous_detNorm F (r + 1)).rpow_const fun c =>
      Or.inl (ne_of_gt (Unfolding.detNorm_pos F (r + 1) c))
  obtain ⟨B, hB⟩ := hC.bddAbove_image hdet.continuousOn
  refine ⟨φ, hφ, ψ, hψ, A * max B 0, mul_nonneg hA (le_max_right _ _),
    fun d c hc => ?_⟩
  have hrow := ENNReal.ofReal_le_ofReal (hΦbound d c hc)
  simp only [ofReal_norm] at hrow
  have hdetB : ENNReal.ofReal (detNorm F (r + 1) c ^ σ) ≤
      ENNReal.ofReal (max B 0) :=
    ENNReal.ofReal_le_ofReal
      ((hB (mem_image_of_mem _ hc)).trans (le_max_left _ _))
  rw [Unfolding.detNorm_mul, Real.mul_rpow
    (Unfolding.detNorm_pos F (r + 1) _).le
    (Unfolding.detNorm_pos F (r + 1) _).le,
    ENNReal.ofReal_mul (Real.rpow_nonneg
      (Unfolding.detNorm_pos F (r + 1) _).le _)]
  calc
    _ ≤ (ENNReal.ofReal A *
          ENNReal.ofReal (gaugeSimpleRootNormProduct F r d ^ (-τ)) *
          ‖φ (gaugeSimpleRootRow F r d)‖ₑ) *
        ‖ψ (singleRow F (d (Fin.last r) : Adeles F))‖ₑ *
        (ENNReal.ofReal
          (detNorm F (r + 1) (gaugeDiagonalPoint F (r + 1) d) ^ σ) *
          ENNReal.ofReal (max B 0)) := by
      exact mul_le_mul (mul_le_mul (hΞbound d c hc) hrow bot_le bot_le)
        (mul_le_mul le_rfl hdetB bot_le bot_le) bot_le bot_le
    _ = _ := by
      rw [ENNReal.ofReal_mul hA]
      ac_rfl

end Langlands.Global.RankinSelbergGlobal
