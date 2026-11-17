import Langlands.Global.RankinSelberg.RectangularArchimedeanBounds
import Langlands.Global.RankinSelberg.AdelicSimpleRootGaugeTorusCoordinates
import Langlands.Global.RankinSelberg.UnfoldingWhittaker

/-! # Corrected torus roots for the rectangular gauge profile -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj ENNReal
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

open PrimitiveAdelicHeight Langlands.GeneralLinear.RectangularIwasawa

local instance correctedRootsSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _

variable (F : Type u) [Field F] [NumberField F]

/-- Multiply a diagonal correction by the leading diagonal, padded by ones. -/
def rectangularCorrectedDiagonal {m n : ℕ} (b : Fin m → Ideles F)
    (c : Fin n → Ideles F) : Fin n → Ideles F :=
  fun i => gaugePaddedIdeles F b i * c i

theorem gaugeSimpleRootIdeles_corrected {m r : ℕ}
    (b : Fin m → Ideles F) (c : Fin (r + 1) → Ideles F) (i : Fin r) :
    gaugeSimpleRootIdeles F r (rectangularCorrectedDiagonal F b c) i =
      gaugeSimpleRootIdeles F r (gaugePaddedIdeles F b) i *
        gaugeSimpleRootIdeles F r c i := by
  simp only [gaugeSimpleRootIdeles, rectangularCorrectedDiagonal, mul_div_mul_comm]

/-- On the retained block the corrected ambient root is the original
block root times the correction root. -/
theorem gaugeSimpleRootIdeles_corrected_leading {t r : ℕ} (h : t < r)
    (b : Fin (t + 1) → Ideles F) (c : Fin (r + 1) → Ideles F)
    (i : Fin (t + 1)) :
    gaugeSimpleRootIdeles F r (rectangularCorrectedDiagonal F b c)
        (Fin.castLE (Nat.succ_le_of_lt h) i) =
      gaugeBlockRootIdeles F t b i *
        gaugeSimpleRootIdeles F r c (Fin.castLE (Nat.succ_le_of_lt h) i) := by
  rw [gaugeSimpleRootIdeles_corrected, gaugeSimpleRootIdeles_padded F h]
  refine Fin.lastCases ?_ (fun q => ?_) i
  · simp [gaugeBlockRootIdeles, GaugeTorusCoordinates.blockRoots_last]
  · simp [gaugeBlockRootIdeles, GaugeTorusCoordinates.blockRoots_castSucc,
      gaugeSimpleRootIdeles, q.isLt]

/-- Recover original block roots by removing the correction root. -/
theorem gaugeBlockRootIdeles_eq_corrected_mul_inverse {t r : ℕ} (h : t < r)
    (b : Fin (t + 1) → Ideles F) (c : Fin (r + 1) → Ideles F)
    (i : Fin (t + 1)) :
    gaugeBlockRootIdeles F t b i =
      gaugeSimpleRootIdeles F r (rectangularCorrectedDiagonal F b c)
        (Fin.castLE (Nat.succ_le_of_lt h) i) *
          (gaugeSimpleRootIdeles F r c (Fin.castLE (Nat.succ_le_of_lt h) i))⁻¹ := by
  rw [gaugeSimpleRootIdeles_corrected_leading F h b c i]
  group

theorem paddedDiagonal_eq_gaugePadded {a d : ℕ} (b : Fin a → Ideles F) :
    paddedDiagonal (d + 1) b =
      (gaugePaddedIdeles F b : Fin (a + d + 1) → Ideles F) := by
  funext i
  induction i using Fin.addCases with
  | left i => simp [paddedDiagonal, gaugePaddedIdeles, i.isLt]
  | right i =>
    have hi : ¬a + i.val < a := by omega
    simp [paddedDiagonal, gaugePaddedIdeles, hi]

/-- The same lower-unipotent factorization supplies all leading diagonal
parameters with the corrected tuple. -/
theorem rectangular_corrected_factorization
    {a d : ℕ} (x : Matrix (Fin d) (Fin a) (Adeles F))
    (U K : AdelicGL F (a + d + 1)) (c : Fin (a + d + 1) → Ideles F)
    (hU : IsUnitriangular U.val)
    (hfac : GeneralLinear.lowerBlockLocalization 1 1 x 1 = U * diagonalGL c * K)
    (b : Fin a → Ideles F) :
    ∃ V : AdelicGL F (a + d + 1), IsUnitriangular V.val ∧
      GeneralLinear.lowerBlockLocalization 1 (diagonalGL b) x 1 =
        V * diagonalGL (rectangularCorrectedDiagonal F b c) * K := by
  rw [lowerBlockLocalization_one_eq_pair] at hfac
  obtain ⟨V, hV, hh⟩ :=
    lowerBlockPair_diagonal_factorization (extendRectangle 1 x) U K c hU hfac b
  refine ⟨V, hV, ?_⟩
  rw [lowerBlockLocalization_one_eq_pair]
  unfold rectangularCorrectedDiagonal
  rw [paddedDiagonal_eq_gaugePadded] at hh
  exact hh

/-- The actual gauge invariances identify the value at a supplied matrix
factorization with its idelic diagonal profile. -/
theorem IsAdelicSimpleRootGauge.eval_matrix_factorization {r : ℕ} {τ : ℝ}
    {Ξ : Points F (r + 1) → ℝ≥0∞} (hΞ : IsAdelicSimpleRootGauge F r τ Ξ)
    (G V K : AdelicGL F (r + 1)) (c : Fin (r + 1) → Ideles F)
    (hV : IsUnitriangular V.val) (hK : K ∈ standardCompact F (r + 1))
    (hfac : G = V * diagonalGL c * K) :
    Ξ ((GeneralLinearGroupPoints.adelicEquiv F (r + 1)).symm G) =
      Ξ (gaugeDiagonalPoint F (r + 1) c) := by
  let E := GeneralLinearGroupPoints.adelicEquiv F (r + 1)
  have hv : E.symm V ∈ unipotentAdelic F (r + 1) := by
    rw [Unfolding.mem_unipotentAdelic_iff]
    simpa only [E, MulEquiv.apply_symm_apply] using hV
  have hk : E.symm K ∈ gaugeStandardCompact F (r + 1) := by
    change E (E.symm K) ∈ standardCompact F (r + 1)
    simpa only [MulEquiv.apply_symm_apply] using hK
  have hd : E.symm (diagonalGL c) = gaugeDiagonalPoint F (r + 1) c := by
    rfl
  rw [hfac, map_mul, map_mul, hd, mul_assoc]
  rw [hΞ.2.2.1 ⟨E.symm V, hv⟩]
  exact hΞ.2.2.2.1 ⟨E.symm K, hk⟩ _

/-- Evaluate the rectangular gauge on every leading diagonal using one
Iwasawa correction chosen independently of that diagonal. -/
theorem IsAdelicSimpleRootGauge.eval_rectangular_diagonal
    {a d : ℕ} {τ : ℝ}
    {Ξ : Points F (a + d + 1) → ℝ≥0∞}
    (hΞ : IsAdelicSimpleRootGauge F (a + d) τ Ξ)
    (x : Matrix (Fin d) (Fin a) (Adeles F))
    (U K : AdelicGL F (a + d + 1)) (c : Fin (a + d + 1) → Ideles F)
    (hU : IsUnitriangular U.val) (hK : K ∈ standardCompact F (a + d + 1))
    (hfac : GeneralLinear.lowerBlockLocalization 1 1 x 1 = U * diagonalGL c * K)
    (b : Fin a → Ideles F) :
    Ξ ((GeneralLinearGroupPoints.adelicEquiv F (a + d + 1)).symm
      (GeneralLinear.lowerBlockLocalization 1 (diagonalGL b) x 1)) =
        Ξ (gaugeDiagonalPoint F (a + d + 1) (rectangularCorrectedDiagonal F b c)) := by
  obtain ⟨V, hV, hh⟩ := rectangular_corrected_factorization F x U K c hU hfac b
  exact hΞ.eval_matrix_factorization F _ V K _ hV hK hh

end Langlands.Global.RankinSelbergGlobal
