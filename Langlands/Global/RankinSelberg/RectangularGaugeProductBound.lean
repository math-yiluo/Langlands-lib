import Langlands.Global.RankinSelberg.RectangleProductMajorant
import Langlands.Global.RankinSelberg.DetNormCompactIntegrals
import Langlands.Global.RankinSelberg.RectangularGaugeTransfer
import Langlands.Global.AdelicGLCompactIwasawa
import Langlands.Group.GL.ReindexCongr

/-! # Product bounds for actual rectangular gauge values -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj Classical NNReal ENNReal
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

open PrimitiveAdelicHeight Langlands.GeneralLinear.RectangularIwasawa Unfolding

variable (F : Type u) [Field F] [NumberField F]

local instance productBoundSchemeAffine (n : ℕ) : IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _

/-- The matrix chart before the harmless rank reindexing in rectangularPoint. -/
def rectangularDiagonalPoint (t d : ℕ) (b : Fin (t + 1) → Ideles F)
    (x : Matrix (Fin d) (Fin (t + 1)) (Adeles F)) : Points F (t + 1 + d + 1) :=
  (GeneralLinearGroupPoints.adelicEquiv F _).symm
    (GeneralLinear.lowerBlockLocalization 1 (diagonalGL b) x 1)

/-- Transport the lower-block integral along an equality of rectangle ranks. -/
theorem lintegral_lowerBlock_rank_congr {a d e : ℕ} (h : d = e)
    (Ξ : Points F (a + e + 1) → ℝ≥0∞) (g : AdelicGL F a) :
    (∫⁻ x : Matrix (Fin d) (Fin a) (Adeles F),
      Ξ ((GeneralLinearGroupPoints.adelicEquiv F (a + e + 1)).symm
        (GeneralLinear.reindex (finCongr (congrArg (fun z => a + z + 1) h))
          (GeneralLinear.lowerBlockLocalization 1 g x 1))) ∂rectangleMeasure F d a) =
      ∫⁻ x : Matrix (Fin e) (Fin a) (Adeles F),
        Ξ ((GeneralLinearGroupPoints.adelicEquiv F (a + e + 1)).symm
          (GeneralLinear.lowerBlockLocalization 1 g x 1)) ∂rectangleMeasure F e a := by
  subst e
  simp only [Langlands.RankinSelberg.reindex_finCongr_self]

/-- On the additive rank decomposition, the actual rectangular integral
is the integral of the same matrix chart without a rank cast. -/
theorem rectangularLIntegral_diagonal_add (t d : ℕ)
    (Ξ : Points F (t + 1 + d + 1) → ℝ≥0∞) (b : Fin (t + 1) → Ideles F) :
    rectangularLIntegral F (by omega : t < t + 1 + d) Ξ
        (gaugeDiagonalPoint F (t + 1) b) =
      ∫⁻ x, Ξ (rectangularDiagonalPoint F t d b x)
        ∂rectangleMeasure F d (t + 1) := by
  have H := lintegral_lowerBlock_rank_congr F
    (show t + 1 + d - (t + 1) = d by omega) Ξ (diagonalGL b)
  have hd : GroupScheme.GeneralLinear.diagonalMatrixUnits (Adeles F) b = diagonalGL b := by
    apply Units.ext
    rfl
  simpa only [rectangularLIntegral, rectangularPoint, rectangularDiagonalPoint,
    gaugeDiagonalPoint, MulEquiv.apply_symm_apply, hd] using H

/-- The determinant norm at a supplied standard Iwasawa factorization
is the determinant norm of its diagonal. -/
theorem detNorm_matrix_factorization {r : ℕ}
    (G V K : AdelicGL F (r + 1)) (c : Fin (r + 1) → Ideles F)
    (hV : IsUnitriangular V.val) (hK : K ∈ standardCompact F (r + 1))
    (hfac : G = V * diagonalGL c * K) :
    detNorm F (r + 1) ((GeneralLinearGroupPoints.adelicEquiv F _).symm G) =
      detNorm F (r + 1) (gaugeDiagonalPoint F (r + 1) c) := by
  let E := GeneralLinearGroupPoints.adelicEquiv F (r + 1)
  have hv : E.symm V ∈ unipotentAdelic F (r + 1) := by
    rw [Unfolding.mem_unipotentAdelic_iff]
    simpa only [E, MulEquiv.apply_symm_apply] using hV
  have hvdet : detNorm F (r + 1) (E.symm V) = 1 :=
    Unfolding.detNorm_unipotent F _ ⟨E.symm V, hv⟩
  have hkdet : detNorm F (r + 1) (E.symm K) = 1 :=
    detNorm_eq_one_of_mem_standardCompact F (by simpa only [E, MulEquiv.apply_symm_apply])
  change detNorm F (r + 1) (E.symm G) = _
  rw [hfac, map_mul, map_mul, Unfolding.detNorm_mul, Unfolding.detNorm_mul,
    hvdet, hkdet, one_mul, mul_one]
  rfl

/-- The lower rectangle does not alter the leading diagonal determinant norm. -/
theorem detNorm_rectangularDiagonalPoint (t d : ℕ) (b : Fin (t + 1) → Ideles F)
    (x : Matrix (Fin d) (Fin (t + 1)) (Adeles F)) :
    detNorm F (t + 1 + d + 1) (rectangularDiagonalPoint F t d b x) =
      detNorm F (t + 1) (gaugeDiagonalPoint F (t + 1) b) := by
  rw [UnequalAnalytic.detNorm_eq_absDet, UnequalAnalytic.detNorm_eq_absDet]
  have he : AdelicGL.determinant F (t + 1 + d + 1)
      (GeneralLinear.lowerBlockLocalization 1 (diagonalGL b) x 1) =
        AdelicGL.determinant F (t + 1) (diagonalGL b) := by
    apply Units.ext
    change Matrix.det (GeneralLinear.lowerBlockLocalization 1 (diagonalGL b) x 1).val =
      Matrix.det (diagonalGL b).val
    rw [GeneralLinear.det_lowerBlockLocalization]
    simp
  simp only [rectangularDiagonalPoint, gaugeDiagonalPoint, MulEquiv.apply_symm_apply]
  change ((IdeleAbsoluteValue.full F (AdelicGL.determinant F _
      (GeneralLinear.lowerBlockLocalization 1 (diagonalGL b) x 1)) : ℝ≥0) : ℝ) =
    ((IdeleAbsoluteValue.full F (AdelicGL.determinant F _ (diagonalGL b)) : ℝ≥0) : ℝ)
  exact congrArg (fun z : Ideles F => ((IdeleAbsoluteValue.full F z : ℝ≥0) : ℝ)) he

/-- Every gauge admits a rank-one product majorant on the actual matrix chart,
with the determinant normalization of exponent tau. -/
theorem IsAdelicSimpleRootGauge.exists_rectangular_product_bound
    [CompactSpace (AdeleQuotient F)] (t d : ℕ) {τ : ℝ}
    {Ξ : Points F (t + 1 + d + 1) → ℝ≥0∞}
    (hΞ : IsAdelicSimpleRootGauge F (t + 1 + d) τ Ξ) :
    ∃ Ψ : RowVector F 1 → ℂ, Ψ ∈ schwartzBruhat F 1 ∧
      ∀ (b : Fin (t + 1) → Ideles F)
        (x : Matrix (Fin d) (Fin (t + 1)) (Adeles F)),
        Ξ (rectangularDiagonalPoint F t d b x) *
            ENNReal.ofReal (detNorm F (t + 1) (gaugeDiagonalPoint F (t + 1) b) ^ τ) ≤
          (∏ i : Fin (t + 1), ‖Ψ (fun _ _ => (gaugeBlockRootIdeles F t b i : Adeles F))‖ₑ) *
            ∏ q : Fin (d * (t + 1)), ‖Ψ (rectangleEntryEquiv F d (t + 1) x q)‖ₑ := by
  obtain ⟨Φ, hΦ, hprofile⟩ := hΞ.2.2.2.2
  obtain ⟨Ψ, hΨ, hmajor⟩ :=
    exists_normalized_rectangular_product_majorant F t d τ hΞ.1 Φ hΦ
  refine ⟨Ψ, hΨ, fun b x => ?_⟩
  let L : AdelicGL F (t + 1 + d + 1) := GeneralLinear.lowerBlockLocalization 1 1 x 1
  obtain ⟨D, _, hD⟩ := exists_compact_iwasawaDiagonal F (t + 1 + d + 1)
    (isCompact_singleton (x := L))
  obtain ⟨c, _, U, K, hU, hK, hfac⟩ := hD L (Set.mem_singleton L)
  obtain ⟨V, hV, hfacb⟩ := rectangular_corrected_factorization F x U K c hU hfac b
  let beta := rectangularCorrectedDiagonal F b c
  have heval := hΞ.eval_rectangular_diagonal F x U K c hU hK hfac b
  have hdet := detNorm_matrix_factorization F _ V K beta hV hK hfacb
  have hlast := last_diagonal_full_norm_le_one F _ V K beta
    (lowerBlockLocalization_hasLastStandardRow F (diagonalGL b) x) hV hK hfacb
  have hweight := normalized_gauge_weight_le_roots F beta τ hΞ.1 hlast
  have hb := hmajor b x U K c hU hK hfac
  have H := (mul_le_mul_of_nonneg_right hweight
    (norm_nonneg (Φ (gaugeSimpleRootRow F _ beta)))).trans hb
  have hnorm : 0 ≤ gaugeSimpleRootNormProduct F (t + 1 + d) beta ^ (-τ) :=
    Real.rpow_nonneg (Finset.prod_nonneg (fun i _ => NNReal.coe_nonneg _)) _
  have hdetnonneg : 0 ≤ detNorm F (t + 1 + d + 1)
      (gaugeDiagonalPoint F (t + 1 + d + 1) beta) ^ τ :=
    Real.rpow_nonneg (detNorm_pos F _ _).le _
  have H' := ENNReal.ofReal_le_ofReal H
  rw [show Ξ (rectangularDiagonalPoint F t d b x) =
      Ξ (gaugeDiagonalPoint F _ beta) from heval, hprofile]
  rw [← detNorm_rectangularDiagonalPoint F t d b x] at ⊢
  change _ * ENNReal.ofReal (detNorm F _
    ((GeneralLinearGroupPoints.adelicEquiv F _).symm _) ^ τ) ≤ _
  rw [hdet]
  have hpnonneg : 0 ≤ ∏ i : Fin (t + 1),
      ‖Ψ (fun _ _ => (gaugeBlockRootIdeles F t b i : Adeles F))‖ :=
    Finset.prod_nonneg (fun i _ => norm_nonneg _)
  simpa only [mul_assoc, ENNReal.ofReal_mul hdetnonneg, ENNReal.ofReal_mul hpnonneg,
    ENNReal.ofReal_mul hnorm, ENNReal.ofReal_prod_of_nonneg (fun _ _ => norm_nonneg _),
    ofReal_norm, mul_comm, mul_left_comm] using H'

/-- Rectangle integration leaves a finite scalar and the leading-root product,
with the determinant exponent shifted by tau. -/
theorem IsAdelicSimpleRootGauge.exists_integrated_rectangular_product_bound
    [CompactSpace (AdeleQuotient F)] (t d : ℕ) {τ : ℝ}
    {Ξ : Points F (t + 1 + d + 1) → ℝ≥0∞}
    (hΞ : IsAdelicSimpleRootGauge F (t + 1 + d) τ Ξ) :
    ∃ Ψ : RowVector F 1 → ℂ, Ψ ∈ schwartzBruhat F 1 ∧
      ∃ M : ℝ≥0∞, M < ⊤ ∧ ∀ (b : Fin (t + 1) → Ideles F) (σ : ℝ),
        (∫⁻ x, Ξ (rectangularDiagonalPoint F t d b x)
            ∂rectangleMeasure F d (t + 1)) *
            ENNReal.ofReal (detNorm F (t + 1) (gaugeDiagonalPoint F (t + 1) b) ^ σ) ≤
          M * ((∏ i : Fin (t + 1),
              ‖Ψ (fun _ _ => (gaugeBlockRootIdeles F t b i : Adeles F))‖ₑ) *
            ENNReal.ofReal (detNorm F (t + 1) (gaugeDiagonalPoint F (t + 1) b) ^ (σ - τ))) := by
  obtain ⟨Ψ, hΨ, hbound⟩ := hΞ.exists_rectangular_product_bound F t d
  let M : ℝ≥0∞ := ∫⁻ x : Matrix (Fin d) (Fin (t + 1)) (Adeles F),
    ∏ q : Fin (d * (t + 1)), ‖Ψ (rectangleEntryEquiv F d (t + 1) x q)‖ₑ
      ∂rectangleMeasure F d (t + 1)
  refine ⟨Ψ, hΨ, M, lintegral_rectangle_prod_enorm_lt_top F d (t + 1) hΨ, ?_⟩
  intro b σ
  let D := detNorm F (t + 1) (gaugeDiagonalPoint F (t + 1) b)
  let B : ℝ≥0∞ := ∏ i : Fin (t + 1),
    ‖Ψ (fun _ _ => (gaugeBlockRootIdeles F t b i : Adeles F))‖ₑ
  have hB : B ≠ ⊤ := (ENNReal.prod_lt_top (fun i _ => enorm_lt_top)).ne
  have H := @MeasureTheory.lintegral_mono _ _ (rectangleMeasure F d (t + 1)) _ _ (hbound b)
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
    lintegral_const_mul' _ _ hB] at H
  have hD : 0 < D := detNorm_pos F _ _
  have hpow : ENNReal.ofReal (D ^ τ) * ENNReal.ofReal (D ^ (σ - τ)) =
      ENNReal.ofReal (D ^ σ) := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hD.le _), ← Real.rpow_add hD]
    congr 2
    ring
  change _ * ENNReal.ofReal (D ^ σ) ≤ M * (B * ENNReal.ofReal (D ^ (σ - τ)))
  rw [← hpow, ← mul_assoc]
  calc
    _ ≤ (B * M) * ENNReal.ofReal (D ^ (σ - τ)) := mul_le_mul' H le_rfl
    _ = _ := by ac_rfl

end Langlands.Global.RankinSelbergGlobal
