import Langlands.Global.RankinSelberg.RealGodementCompactKernel
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! # Compact approximation by real Godement sections -/

noncomputable section

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open GramFormula PrincipalSeriesExtension MeasureTheory Metric Set
open scoped ContDiff Manifold Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

variable {m : ℕ}

local notation "M" => Matrix (Fin m) (Fin m) ℝ
local notation "G" => Langlands.GeneralLinear m ℝ
local notation "H" => Langlands.GeneralLinear (m + 1) ℝ

/-- The product of the scalar Gram and angular cutoffs on the lower group. -/
def gramAngularWeight (β : M → ℝ) (b : ℝ → ℝ) (h : G) : ℝ :=
  β (lowerGram h) * b (lowerAngle h)

theorem continuous_gramAngularWeight {β : M → ℝ} {b : ℝ → ℝ}
    (hβ : Continuous β) (hb : Continuous b) : Continuous (gramAngularWeight β b) :=
  (hβ.comp continuous_lowerGram).mul (hb.comp continuous_lowerAngle)

theorem hasCompactSupport_gramAngularWeight {β : M → ℝ} (b : ℝ → ℝ) {S : Set M}
    (hS : IsCompact S) (hUnit : ∀ y ∈ S, IsUnit y) (hβZero : ∀ y ∉ S, β y = 0) :
    HasCompactSupport (gramAngularWeight β b) := by
  have hK := isCompact_lowerGram_preimage hS hUnit
  apply hK.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hK.isClosed
  intro h hh
  by_contra! hOutside
  exact hh (by simp [gramAngularWeight, hβZero _ hOutside])

private theorem lowerGram_one : lowerGram (1 : G) = 1 := by
  simp [lowerGram]

private theorem lowerAngle_one : lowerAngle (1 : G) = 0 := by
  have h : signedOrthogonal (1 : M) = 1 := by
    simpa [signReal] using signedOrthogonal_mul (b := (1 : M)) (κ := (1 : M))
      Matrix.blockTriangular_one (fun _ => by simp) (by simp)
  simp only [lowerAngle, inv_one, Units.val_one, h, offDiagonalSquare]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j hj
  simp [(Finset.mem_erase.mp hj).1.symm]

theorem sectionValue_gramTest_lowerCutoff [MeasurableSpace (Langlands.GeneralLinear m ℝ)]
    (μ : Measure (Langlands.GeneralLinear m ℝ)) (c : RealCharacterData) (ds : List RealBlock)
    {F : H → ℂ}
    (hF : F ∈ principalSeries ℝ (m + 1) (realPositionCharacter (.character c :: ds)))
    (β : M → ℝ) (b : ℝ → ℝ) {k : H} (hk : k ∈ unitaryCompact ℝ (m + 1)) :
    sectionValue μ c (lowerCutoff ds b) (gramTest c F β) k =
      ∫ h : G, (gramAngularWeight β b h : ℂ) * compactKernel ds F h k ∂μ := by
  rw [sectionValue_gramTest μ c ds hF]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro h
  have hD : (Real.sqrt |h.val.det| : ℂ) = ((|h.val.det| : ℝ) : ℂ) ^ (1 / 2 : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (abs_nonneg _)]
    norm_num
  dsimp only
  rw [rowGram_rowPoint_of_orthogonal _ hk, lowerCutoff_factor, compactKernel, hD]
  simp only [gramAngularWeight, Complex.ofReal_mul, lowerGram]
  ring

theorem integrable_weightedKernel [MeasurableSpace (Langlands.GeneralLinear m ℝ)]
    [BorelSpace (Langlands.GeneralLinear m ℝ)] (μ : Measure (Langlands.GeneralLinear m ℝ))
    [IsFiniteMeasureOnCompacts μ] (c : RealCharacterData) (ds : List RealBlock) {F : H → ℂ}
    (hF : F ∈ principalSeries ℝ (m + 1) (realPositionCharacter (.character c :: ds))) (k : H)
    {w : G → ℝ} (hw : Continuous w) (hws : HasCompactSupport w) :
    Integrable (fun h : G => (w h : ℂ) * compactKernel ds F h k) μ :=
  ((Complex.continuous_ofReal.comp hw).mul ((continuous_compactKernel ds c hF).comp
    (continuous_id.prodMk continuous_const))).integrable_of_hasCompactSupport
      (hws.comp_left (g := Complex.ofReal) Complex.ofReal_zero).mul_right

private theorem exists_compact_cutoffs [MeasurableSpace (Langlands.GeneralLinear m ℝ)]
    [BorelSpace (Langlands.GeneralLinear m ℝ)] (μ : Measure (Langlands.GeneralLinear m ℝ))
    [IsFiniteMeasureOnCompacts μ] [Measure.IsOpenPosMeasure μ]
    (c : RealCharacterData) (ds : List RealBlock) {F : H → ℂ}
    (hF : F ∈ principalSeries ℝ (m + 1) (realPositionCharacter (.character c :: ds)))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (S : Set M) (β : M → ℝ) (b : ℝ → ℝ),
      IsCompact S ∧ (∀ y ∈ S, IsUnit y) ∧ ContDiff ℝ ∞ β ∧ (∀ y ∉ S, β y = 0) ∧
      ContDiff ℝ ∞ b ∧ ∀ k ∈ unitaryCompact ℝ (m + 1),
        ‖sectionValue μ c (lowerCutoff ds b) (gramTest c F β) k - F k‖ < ε := by
  have hOpen : IsOpen {y : M | IsUnit y} := isOpen_setOf_isUnit_matrix
  obtain ⟨r, hr, hrUnit⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (hOpen.mem_nhds (show (1 : M) ∈ {y | IsUnit y} from isUnit_one))
  let S : Set M := closedBall 1 r
  have hS : IsCompact S := isCompact_closedBall _ _
  have hUnit (y : M) (hy : y ∈ S) : IsUnit y := hrUnit hy
  obtain ⟨δ, hδ, hError⟩ := realGodementCompactKernel m c ds F S hF hS hUnit
    (ε / 2) (by positivity)
  let ρ : ℝ := min r (δ / 4)
  have hρ : 0 < ρ := lt_min hr (by positivity)
  let β₀ : ContDiffBump (1 : M) := ⟨ρ / 2, ρ, by positivity, by linarith⟩
  let b : ContDiffBump (0 : ℝ) := ⟨δ / 8, δ / 4, by positivity, by linarith⟩
  have hβ₀Zero (y : M) (hy : y ∉ S) : β₀ y = 0 := by
    apply β₀.zero_of_le_dist
    exact (min_le_left r (δ / 4)).trans (not_le.mp hy).le
  let w₀ : G → ℝ := gramAngularWeight β₀ b
  have hw₀ : Continuous w₀ := continuous_gramAngularWeight β₀.continuous b.continuous
  have hw₀S : HasCompactSupport w₀ := hasCompactSupport_gramAngularWeight b hS hUnit hβ₀Zero
  let Z : ℝ := ∫ h : G, w₀ h ∂μ
  have hZ : 0 < Z := by
    apply hw₀.integral_pos_of_hasCompactSupport_nonneg_nonzero hw₀S
      (fun _ => mul_nonneg β₀.nonneg b.nonneg) (x := (1 : G))
    change β₀ (lowerGram (1 : G)) * b (lowerAngle (1 : G)) ≠ 0
    rw [lowerGram_one, lowerAngle_one, β₀.one_of_mem_closedBall
      (mem_closedBall_self β₀.rIn_pos.le), b.one_of_mem_closedBall (mem_closedBall_self b.rIn_pos.le),
      one_mul]
    exact one_ne_zero
  let β : M → ℝ := fun y => Z⁻¹ * β₀ y
  have hβ : ContDiff ℝ ∞ β := contDiff_const.mul β₀.contDiff
  have hβZero (y : M) (hy : y ∉ S) : β y = 0 := by simp [β, hβ₀Zero y hy]
  refine ⟨S, β, b, hS, hUnit, hβ, hβZero, b.contDiff, ?_⟩
  let w : G → ℝ := gramAngularWeight β b
  have hw : Continuous w := continuous_gramAngularWeight hβ.continuous b.continuous
  have hwS : HasCompactSupport w := hasCompactSupport_gramAngularWeight b hS hUnit hβZero
  have hwInt : Integrable w μ := hw.integrable_of_hasCompactSupport hwS
  have hwOne : ∫ h : G, w h ∂μ = 1 := by
    have heq : w = fun h => Z⁻¹ * w₀ h := funext fun h => mul_assoc _ _ _
    rw [heq, integral_const_mul]
    exact inv_mul_cancel₀ hZ.ne'
  have hwPos (h : G) : 0 ≤ w h :=
    mul_nonneg (mul_nonneg (inv_nonneg.mpr hZ.le) β₀.nonneg) b.nonneg
  intro k hk
  have hkInt := integrable_weightedKernel μ c ds hF k hw hwS
  have hkConst : Integrable (fun h : G => (w h : ℂ) * F k) μ := hwInt.ofReal.mul_const _
  have hConst : ∫ h : G, (w h : ℂ) * F k ∂μ = F k := by
    rw [integral_mul_const, integral_complex_ofReal, hwOne, Complex.ofReal_one, one_mul]
  have hDiff : sectionValue μ c (lowerCutoff ds b) (gramTest c F β) k - F k =
      ∫ h : G, (w h : ℂ) * (compactKernel ds F h k - F k) ∂μ := by
    simp only [mul_sub, integral_sub hkInt hkConst, hConst, sectionValue_gramTest_lowerCutoff μ c ds hF β b hk]
    rfl
  rw [hDiff]
  have hPoint (h : G) : ‖(w h : ℂ) * (compactKernel ds F h k - F k)‖ ≤ w h * (ε / 2) := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hwPos h)]
    by_cases hwZero : w h = 0
    · simp [hwZero]
    · have hβ₀Nonzero : β₀ (lowerGram h) ≠ 0 := by
        intro hz
        exact hwZero (by simp [w, gramAngularWeight, β, hz])
      have hbNonzero : b (lowerAngle h) ≠ 0 := by
        intro hz
        exact hwZero (by simp [w, gramAngularWeight, hz])
      have hMem : lowerGram h ∈ S := by
        by_contra! hOut
        exact hβ₀Nonzero (hβ₀Zero _ hOut)
      have hG : dist (lowerGram h) 1 < ρ :=
        lt_of_not_ge (fun hle => hβ₀Nonzero (β₀.zero_of_le_dist hle))
      have hB : lowerAngle h < δ / 4 := by
        apply lt_of_not_ge
        intro hl
        apply hbNonzero
        apply b.zero_of_le_dist
        have hNonneg : 0 ≤ lowerAngle h := offDiagonalSquare_nonneg _
        rwa [Real.dist_eq, sub_zero, abs_of_nonneg hNonneg]
      have hSmall : dist (lowerGram h) 1 + lowerAngle h < δ := by
        have hρ' : ρ ≤ δ / 4 := min_le_right _ _
        linarith
      exact mul_le_mul_of_nonneg_left (hError h hMem hSmall k hk).le (hwPos h)
  have hIntegral := norm_integral_le_of_norm_le (hwInt.mul_const (ε / 2))
    (Filter.Eventually.of_forall hPoint)
  rw [integral_mul_const, hwOne, one_mul] at hIntegral
  exact hIntegral.trans_lt (by linarith)

/-- Compactly supported real Godement sections approximate every smooth upper
position principal-series vector uniformly on the orthogonal group. -/
def RealGodementCompactApproximationStatement : Prop :=
  ∀ (m : ℕ) [MeasurableSpace (Langlands.GeneralLinear m ℝ)]
    [BorelSpace (Langlands.GeneralLinear m ℝ)] (μ : Measure (Langlands.GeneralLinear m ℝ))
    [IsFiniteMeasureOnCompacts μ] [Measure.IsOpenPosMeasure μ]
    (c : RealCharacterData) (ds : List RealBlock) (F : Langlands.GeneralLinear (m + 1) ℝ → ℂ),
    F ∈ principalSeries ℝ (m + 1) (realPositionCharacter (.character c :: ds)) →
    ∀ ε > (0 : ℝ), ∃ (S : Set (Matrix (Fin m) (Fin m) ℝ))
      (β : Matrix (Fin m) (Fin m) ℝ → ℝ) (b : ℝ → ℝ),
      IsCompact S ∧ (∀ y ∈ S, IsUnit y) ∧ ContDiff ℝ ∞ β ∧ (∀ y ∉ S, β y = 0) ∧
      ContDiff ℝ ∞ b ∧ ∀ k ∈ unitaryCompact ℝ (m + 1),
        ‖sectionValue μ c (lowerCutoff ds b) (gramTest c F β) k - F k‖ < ε

theorem realGodementCompactApproximation : RealGodementCompactApproximationStatement := by
  intro m _ _ μ _ _ c ds F hF ε hε
  exact exists_compact_cutoffs μ c ds hF ε hε

end Langlands.Global.RankinSelbergGlobal.RealGodement
