import Langlands.Global.RankinSelberg.IdeleDenominatorNorm
import Langlands.Global.RankinSelberg.AdelicSimpleRootGaugePaddedIntegrand

/-! # Determinant normalization of the rectangular gauge weight -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj Classical NNReal
set_option autoImplicit false

namespace Langlands.GeneralLinear.RectangularIwasawa

/-- The final row of a matrix is the final standard basis row. -/
def HasLastStandardRow {R : Type u} [CommRing R] {r : ℕ}
    (G : Langlands.GeneralLinear (r + 1) R) : Prop :=
  ∀ j, G (Fin.last r) j =
    (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (Fin.last r) j

theorem last_diagonal_eq_inverse_entry
    {R : Type u} [CommRing R] {r : ℕ}
    (G V K : Langlands.GeneralLinear (r + 1) R) (c : Fin (r + 1) → Rˣ)
    (hG : HasLastStandardRow G) (hV : Global.PrimitiveAdelicHeight.IsUnitriangular V.val)
    (hfac : G = V * Global.PrimitiveAdelicHeight.diagonalGL c * K) :
    (c (Fin.last r) : R) = K⁻¹ (Fin.last r) (Fin.last r) := by
  have he : V * Global.PrimitiveAdelicHeight.diagonalGL c = G * K⁻¹ := by
    rw [hfac]
    group
  have hd : (V * Global.PrimitiveAdelicHeight.diagonalGL c) (Fin.last r) (Fin.last r) =
      (c (Fin.last r) : R) := by
    change (V.val * (Global.PrimitiveAdelicHeight.diagonalGL c).val) _ _ = _
    rw [Global.PrimitiveAdelicHeight.diagonalGL, Matrix.mul_diagonal, hV.2, one_mul]
  have hh := congrArg (fun B : Langlands.GeneralLinear (r + 1) R =>
    B (Fin.last r) (Fin.last r)) he
  rw [hd] at hh
  change (c (Fin.last r) : R) = (G.val * (K⁻¹).val) (Fin.last r) (Fin.last r) at hh
  have hrow : ∀ j, G (Fin.last r) j =
      (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (Fin.last r) j := hG
  simpa [Matrix.mul_apply, hrow, Matrix.one_apply] using hh

end Langlands.GeneralLinear.RectangularIwasawa

namespace Langlands.Global.RankinSelbergGlobal

open PrimitiveAdelicHeight Langlands.GeneralLinear.RectangularIwasawa

variable (F : Type u) [Field F] [NumberField F]

theorem standardCompact_entry_finite_integral {n : ℕ}
    (K : AdelicGL F n) (hK : K ∈ standardCompact F n) (i j : Fin n) :
    (K i j).2 ∈ integralFiniteAdeles F := by
  have hk := ((mem_standardCompact_iff F n K).mp hK).2
  change (∀ p q, (K p q).2 ∈ integralFiniteAdeles F) ∧
    (∀ p q, (K⁻¹ p q).2 ∈ integralFiniteAdeles F) at hk
  exact hk.1 i j

theorem standardCompact_entry_archimedean_norm_le_one {n : ℕ}
    (K : AdelicGL F n) (hK : K ∈ standardCompact F n) (i j : Fin n) :
    ‖archimedeanAdeleProjection F (K i j)‖ ≤ 1 := by
  have hu := (mem_standardInfiniteCompact_iff F n _).mp
    ((mem_standardCompact_iff F n K).mp hK).1
  rw [Prod.norm_def, max_le_iff]
  constructor
  · apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro v
    exact Langlands.LinearAlgebra.TriangularUnitary.norm_le_one_of_mem_unitaryGroup
      (hu.1 v) i j
  · apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro v
    exact Langlands.LinearAlgebra.TriangularUnitary.norm_le_one_of_mem_unitaryGroup
      (hu.2 v) i j

/-- The final Iwasawa diagonal of a matrix with final standard basis row
has full idele norm at most one. -/
theorem last_diagonal_full_norm_le_one {r : ℕ}
    (G V K : AdelicGL F (r + 1)) (c : Fin (r + 1) → Ideles F)
    (hG : HasLastStandardRow G) (hV : IsUnitriangular V.val)
    (hK : K ∈ standardCompact F (r + 1))
    (hfac : G = V * diagonalGL c * K) :
    ((IdeleAbsoluteValue.full F (c (Fin.last r)) : ℝ≥0) : ℝ) ≤ 1 := by
  have he := last_diagonal_eq_inverse_entry G V K c hG hV hfac
  have hKi := (standardCompact F _).inv_mem hK
  apply full_idele_norm_le_one F
  · rw [he]
    exact standardCompact_entry_finite_integral F K⁻¹ hKi _ _
  · unfold ideleArchimedeanNorm
    rw [he]
    exact standardCompact_entry_archimedean_norm_le_one F K⁻¹ hKi _ _

theorem lowerBlockLocalization_hasLastStandardRow
    {a d : ℕ} (g : AdelicGL F a) (x : Matrix (Fin d) (Fin a) (Adeles F)) :
    HasLastStandardRow (GeneralLinear.lowerBlockLocalization 1 g x 1) := by
  intro j
  have hl : GeneralLinear.lowerBlockLast a d (0 : Fin 1) = Fin.last (a + d) := by
    apply Fin.ext
    simp [GeneralLinear.lowerBlockLast]
  rw [← hl]
  exact lowerBlockLocalization_final_row g x (0 : Fin 1) j

private theorem prod_diagonal_eq_last_roots {r : ℕ} (c : Fin (r + 1) → Ideles F) :
    ∏ i, c i = c (Fin.last r) ^ (r + 1) *
      ∏ i : Fin r, gaugeSimpleRootIdeles F r c i ^ (i.val + 1) := by
  rw [GaugeTorusCoordinates.prod_eq_prod_blockRoots_pow r c, Fin.prod_univ_castSucc]
  simp only [GaugeTorusCoordinates.blockRoots_castSucc,
    GaugeTorusCoordinates.blockRoots_last, Fin.val_castSucc, Fin.val_last]
  exact mul_comm _ _

theorem detNorm_diagonal_eq_last_roots {r : ℕ} (c : Fin (r + 1) → Ideles F) :
    detNorm F (r + 1) (gaugeDiagonalPoint F (r + 1) c) =
      (((IdeleAbsoluteValue.full F (c (Fin.last r)) : ℝ≥0) : ℝ) ^ (r + 1)) *
        ∏ i : Fin r,
          (((IdeleAbsoluteValue.full F (gaugeSimpleRootIdeles F r c i) : ℝ≥0) : ℝ) ^
            (i.val + 1)) := by
  rw [detNorm_gaugeDiagonalPoint]
  have hh := congrArg (fun z : Ideles F => ((IdeleAbsoluteValue.full F z : ℝ≥0) : ℝ))
    (prod_diagonal_eq_last_roots F c)
  simpa only [map_prod, map_mul, map_pow, Units.val_mul, Units.coe_prod,
    Units.val_pow_eq_pow_val, NNReal.coe_prod, NNReal.coe_mul, NNReal.coe_pow] using hh

/-- Determinant normalization leaves only fixed nonnegative powers of
the actual simple-root idele norms. -/
theorem normalized_gauge_weight_le_roots {r : ℕ}
    (c : Fin (r + 1) → Ideles F) (τ : ℝ) (hτ : 0 ≤ τ)
    (hlast : ((IdeleAbsoluteValue.full F (c (Fin.last r)) : ℝ≥0) : ℝ) ≤ 1) :
    detNorm F (r + 1) (gaugeDiagonalPoint F (r + 1) c) ^ τ *
        gaugeSimpleRootNormProduct F r c ^ (-τ) ≤
      ∏ i : Fin r,
        (((IdeleAbsoluteValue.full F (gaugeSimpleRootIdeles F r c i) : ℝ≥0) : ℝ) ^
          ((i.val : ℝ) * τ)) := by
  let A : Fin r → ℝ := fun i =>
    ((IdeleAbsoluteValue.full F (gaugeSimpleRootIdeles F r c i) : ℝ≥0) : ℝ)
  let L : ℝ := ((IdeleAbsoluteValue.full F (c (Fin.last r)) : ℝ≥0) : ℝ)
  have hA : ∀ i, 0 < A i := fun i => IdeleAbsoluteValue.full_pos F _
  have hL : 0 ≤ L := NNReal.coe_nonneg _
  have hweights : (∏ i, A i) ^ (-τ) * (∏ i, A i ^ (i.val + 1)) ^ τ =
      ∏ i, A i ^ ((i.val : ℝ) * τ) := by
    rw [GaugeCoordinateRestriction.prod_rpow_weight A hA (fun i => i.val + 1) τ τ]
    apply Finset.prod_congr rfl
    intro i _
    congr 1
    push_cast
    ring
  have hlastpow : (L ^ (r + 1)) ^ τ ≤ 1 :=
    Real.rpow_le_one (pow_nonneg hL _) (pow_le_one₀ hL hlast) hτ
  rw [detNorm_diagonal_eq_last_roots]
  change (L ^ (r + 1) * ∏ i, A i ^ (i.val + 1)) ^ τ * (∏ i, A i) ^ (-τ) ≤ _
  rw [Real.mul_rpow (pow_nonneg hL _)
    (Finset.prod_nonneg (fun i _ => pow_nonneg (hA i).le _))]
  calc
    _ = (L ^ (r + 1)) ^ τ *
        ((∏ i, A i) ^ (-τ) * (∏ i, A i ^ (i.val + 1)) ^ τ) := by ring
    _ = (L ^ (r + 1)) ^ τ * ∏ i, A i ^ ((i.val : ℝ) * τ) := by rw [hweights]
    _ ≤ 1 * ∏ i, A i ^ ((i.val : ℝ) * τ) :=
      mul_le_mul_of_nonneg_right hlastpow
        (Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (hA i).le _))
    _ = _ := one_mul _

end Langlands.Global.RankinSelbergGlobal
