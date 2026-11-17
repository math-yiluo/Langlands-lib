import Langlands.Global.RankinSelberg.RectangularCorrectedRoots

/-! # Two-sided bounds on rectangular diagonal corrections -/

noncomputable section
universe u v
set_option autoImplicit false

namespace Langlands.GeneralLinear.RectangularIwasawa

open Langlands.Global.PrimitiveAdelicHeight

variable {𝕜 : Type u} [NormedField 𝕜] {I : Type v} {a d : ℕ}

/-- A unit tuple and its coordinatewise inverse satisfy the same norm bound. -/
def IsNormBoundedUnitTuple (c : I → 𝕜ˣ) (C : ℝ) : Prop :=
  ∀ i, ‖(c i : 𝕜)‖ ≤ C ∧ ‖(((c i)⁻¹ : 𝕜ˣ) : 𝕜)‖ ≤ C

theorem IsNormBoundedUnitTuple.div_norm_le
    {c : I → 𝕜ˣ} {C : ℝ} (hc : IsNormBoundedUnitTuple c C) (i j : I) :
    ‖((c i / c j : 𝕜ˣ) : 𝕜)‖ ≤ C ^ 2 := by
  rw [div_eq_mul_inv, Units.val_mul, norm_mul, pow_two]
  exact mul_le_mul (hc i).1 (hc j).2 (norm_nonneg _) ((norm_nonneg _).trans (hc i).1)

private theorem diagonal_correction_bounds
    (U : Langlands.GeneralLinear (a + d) 𝕜) (c : Fin (a + d) → 𝕜ˣ)
    (hU : IsUnitriangular U.val) (C : ℝ)
    (hb : ∀ i : Fin (a + d),
      ‖(U * diagonalGL c) i i‖ ≤ C ∧ ‖(U * diagonalGL c)⁻¹ i i‖ ≤ C) :
    IsNormBoundedUnitTuple c C := by
  let B := U * diagonalGL c
  have hB : B.val.IsUpperTriangular :=
    hU.1.mul (Matrix.blockTriangular_diagonal _)
  have hd (i : Fin (a + d)) : B i i = (c i : 𝕜) := by
    change (U.val * (diagonalGL c).val) i i = _
    rw [diagonalGL, Matrix.mul_diagonal, hU.2 i, one_mul]
  intro i
  have hu : diagonalUnit B hB i = c i := Units.ext (hd i)
  have hui := congrArg (fun z : 𝕜ˣ => ((z⁻¹ : 𝕜ˣ) : 𝕜)) hu
  change B⁻¹ i i = ((c i)⁻¹ : 𝕜ˣ) at hui
  have hbi := hb i
  change ‖B i i‖ ≤ C ∧ ‖B⁻¹ i i‖ ≤ C at hbi
  rwa [hd, hui] at hbi

/-- A lower-unipotent Iwasawa correction is bounded in both directions
by the rectangular entry bound, with a rank factor for ordinary norms. -/
theorem norm_bounded_diagonal_correction
    (x : Matrix (Fin d) (Fin a) 𝕜) (U K : Langlands.GeneralLinear (a + d) 𝕜)
    (c : Fin (a + d) → 𝕜ˣ) (hU : IsUnitriangular U.val)
    (hK : ∀ i j, ‖K i j‖ ≤ 1) (hKi : ∀ i j, ‖K⁻¹ i j‖ ≤ 1)
    (hfac : lowerBlockPair 1 x 1 = U * diagonalGL c * K)
    (C : ℝ) (hC : 1 ≤ C) (hx : ∀ i j, ‖x i j‖ ≤ C) :
    IsNormBoundedUnitTuple c ((a + d) * C) := by
  apply diagonal_correction_bounds U c hU
  intro i
  simpa only [Nat.cast_add] using
    norm_factor_entries_le (lowerBlockPair 1 x 1) (U * diagonalGL c) K hfac
      C (zero_le_one.trans hC) (norm_lowerBlockPair_one_entry_le x C hC hx)
      (norm_lowerBlockPair_one_inv_entry_le x C hC hx) hK hKi i i

/-- The ultrametric correction bound has constant one, in both directions. -/
theorem norm_bounded_diagonal_correction_ultrametric
    [IsUltrametricDist 𝕜]
    (x : Matrix (Fin d) (Fin a) 𝕜) (U K : Langlands.GeneralLinear (a + d) 𝕜)
    (c : Fin (a + d) → 𝕜ˣ) (hU : IsUnitriangular U.val)
    (hK : ∀ i j, ‖K i j‖ ≤ 1) (hKi : ∀ i j, ‖K⁻¹ i j‖ ≤ 1)
    (hfac : lowerBlockPair 1 x 1 = U * diagonalGL c * K)
    (C : ℝ) (hC : 1 ≤ C) (hx : ∀ i j, ‖x i j‖ ≤ C) :
    IsNormBoundedUnitTuple c C := by
  apply diagonal_correction_bounds U c hU
  intro i
  exact norm_factor_entries_le_ultrametric (lowerBlockPair 1 x 1) (U * diagonalGL c) K hfac
    C (zero_le_one.trans hC) (norm_lowerBlockPair_one_entry_le x C hC hx)
    (norm_lowerBlockPair_one_inv_entry_le x C hC hx) hK hKi i i

end Langlands.GeneralLinear.RectangularIwasawa
