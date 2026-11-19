import Langlands.Global.RankinSelberg.RealGodementRowDescent
import Langlands.Representation.Archimedean.RealRankOneStandardModule
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! # Generation by compactly supported real Godement sections from rank one -/

noncomputable section

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open MeasureTheory Metric Set
open scoped Matrix.Norms.Operator Manifold ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

namespace GLTwo

local notation "G₁" => Langlands.GeneralLinear 1 ℝ
local notation "G₂" => Langlands.GeneralLinear 2 ℝ
local notation "X" => Matrix (Fin 1) (Fin 2) ℝ
local notation "χ" => RealRankOneStandardModule.characterVector

private def rowSquare (x : X) : ℝ := ∑ j : Fin 2, x 0 j ^ 2

private theorem contDiff_rowSquare : ContDiff ℝ ∞ rowSquare := by
  unfold rowSquare
  refine ContDiff.sum fun j _ => ?_
  let L : X →ₗ[ℝ] ℝ :=
    { toFun := fun x => x 0 j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  exact L.toContinuousLinearMap.contDiff.pow 2

private def shell : Set X :=
  rowSquare ⁻¹' Icc (1 / 2) (3 / 2)

private theorem isClosed_shell : IsClosed shell :=
  isClosed_Icc.preimage contDiff_rowSquare.continuous

private theorem isCompact_shell : IsCompact shell := by
  apply ((isCompact_Icc : IsCompact (Icc (-2 : ℝ) 2)).matrix).of_isClosed_subset isClosed_shell
  intro x hx i j
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  have hd : x 0 j ^ 2 ≤ 3 / 2 :=
    (Finset.single_le_sum (fun k _ => sq_nonneg (x 0 k)) (Finset.mem_univ j)).trans hx.2
  exact ⟨by nlinarith [sq_nonneg (x 0 j + 1)], by nlinarith [sq_nonneg (x 0 j - 1)]⟩

private theorem fullRowRank_of_mem_shell {x : X} (hx : x ∈ shell) :
    HasFullRowRank x := by
  have hne : rowSquare x ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hx.1)
  refine ⟨(rowSquare x)⁻¹ • x.transpose, ?_⟩
  ext i j
  have hi : i = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  subst i
  subst j
  rw [Matrix.mul_smul, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul]
  change (rowSquare x)⁻¹ * (∑ j : Fin 2, x 0 j * x 0 j) = 1
  simp only [← pow_two]
  exact inv_mul_cancel₀ hne

private def bump : ContDiffBump (1 : ℝ) :=
  ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

private theorem bump_rowSquare_eq_zero {x : X} (hx : x ∉ shell) :
    bump (rowSquare x) = 0 := by
  apply bump.zero_of_le_dist
  change (1 : ℝ) / 4 ≤ dist (rowSquare x) 1
  rw [Real.dist_eq]
  by_contra! h
  exact hx ⟨by linarith [(abs_lt.mp h).1], by linarith [(abs_lt.mp h).2]⟩

private theorem det_GLone (h : G₁) : (Matrix.GeneralLinearGroup.det h : ℝ) = h.val 0 0 := by
  change h.val.det = _
  exact Matrix.det_fin_one _

private theorem rowSquare_rowPoint (h : G₁) {k : G₂} (hk : k ∈ unitaryCompact ℝ 2) :
    rowSquare (rowPoint h.val k) = (Matrix.GeneralLinearGroup.det h : ℝ) ^ 2 := by
  have hOrth : k.val * k.val.transpose = 1 :=
    GramFormula.mul_transpose_eq_one_of_mem hk
  have hNorm := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 1 1) hOrth
  change (k.val * k.val.transpose) 1 1 = (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 1 at hNorm
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq, ← pow_two] at hNorm
  rw [det_GLone]
  simp only [rowSquare, rowPoint, Matrix.mul_apply, Fin.sum_univ_one, lastRows, mul_pow]
  rw [← Finset.mul_sum]
  change (h.val 0 0) ^ 2 * (∑ j : Fin 2, k.val 1 j ^ 2) = _
  rw [hNorm, mul_one]

private def lowerDiagonal (h : G₁) : Fin 2 → ℝˣ :=
  Fin.cases 1 (fun _ => Matrix.GeneralLinearGroup.det h)

private theorem lastRows_lowerDiagonal (h : G₁) (g : G₂) :
    lastRows (Iwasawa.diagonalUnits (lowerDiagonal h) * g).val = rowPoint h.val g := by
  ext i j
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  change ((Iwasawa.diagonalUnits (lowerDiagonal h) : G₂).val * g.val) (0 : Fin 1).succ j =
    (h.val * lastRows g.val) 0 j
  rw [Iwasawa.diagonalUnits_val, Matrix.diagonal_mul]
  simp only [lowerDiagonal, Fin.cases_succ, det_GLone, Matrix.mul_apply, Fin.sum_univ_one, lastRows]

private theorem det_lowerDiagonal (h : G₁) :
    Matrix.GeneralLinearGroup.det (Iwasawa.diagonalUnits (lowerDiagonal h)) =
      Matrix.GeneralLinearGroup.det h := by
  apply Units.ext
  change (Iwasawa.diagonalUnits (lowerDiagonal h) : G₂).val.det =
    (Matrix.GeneralLinearGroup.det h : ℝ)
  rw [Iwasawa.diagonalUnits_val, Matrix.det_diagonal, Fin.prod_univ_two]
  change (1 : ℝ) * (Matrix.GeneralLinearGroup.det h : ℝ) = _
  rw [one_mul]

private theorem lowerCharacter_cancel (c d : RealCharacterData) (h : G₁) :
    χ d h⁻¹ * determinantWeight c (1 : ℂ) h *
        principalSeriesCharacter ℝ 2 (realPositionCharacter [.character c, .character d])
          (lowerDiagonal h) =
      determinantWeight c (1 / 2) (Iwasawa.diagonalUnits (lowerDiagonal h)) := by
  let t := Matrix.GeneralLinearGroup.det h
  let b : ℂ := (|(t : ℝ)| : ℝ)
  have hb : b ≠ 0 := Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr t.ne_zero)
  have hLower : determinantWeight c (1 : ℂ) h = (c.character t : ℂ) * b ^ (1 : ℂ) := rfl
  have hUpper : determinantWeight c (1 / 2) (Iwasawa.diagonalUnits (lowerDiagonal h)) =
      (c.character t : ℂ) * b ^ (1 / 2 : ℂ) := by
    change (c.character _ : ℂ) * ((|(_ : ℝ)| : ℝ) : ℂ) ^ (1 / 2 : ℂ) = _
    rw [det_lowerDiagonal h]
  have hInv : χ d h⁻¹ = (d.character t : ℂ)⁻¹ := by
    simp only [RealRankOneStandardModule.characterVector, map_inv, Units.val_inv_eq_inv_val, t]
  have hFactor : principalSeriesCharacter ℝ 2
      (realPositionCharacter [.character c, .character d]) (lowerDiagonal h) =
        (d.character t : ℂ) * b ^ (-(1 / 2) : ℂ) := by
    rw [principalSeriesCharacter, Fin.prod_univ_two]
    have h0 : lowerDiagonal h (0 : Fin 2) = 1 := rfl
    have h1 : lowerDiagonal h (1 : Fin 2) = t := rfl
    have i0 : ((0 : Fin 2) : ℕ) = 0 := rfl
    have i1 : ((1 : Fin 2) : ℕ) = 1 := rfl
    simp only [h0, h1, i0, i1, realPositionCharacter, map_one, Real.norm_eq_abs,
      Units.val_one, abs_one, Complex.ofReal_one, Complex.one_cpow, Module.finrank_self,
      pow_one, mul_one, one_mul]
    rw [show (((2 : ℕ) : ℂ) - 1) / 2 - ((1 : ℕ) : ℂ) = -(1 / 2) by norm_num]
  rw [hInv, hLower, hFactor, hUpper]
  calc
    _ = (c.character t : ℂ) * ((d.character t : ℂ)⁻¹ * d.character t) *
        (b ^ (1 : ℂ) * b ^ (-(1 / 2) : ℂ)) := by ring
    _ = _ := by
      rw [inv_mul_cancel₀ (d.character t).ne_zero, mul_one, ← Complex.cpow_add _ _ hb]
      congr 2
      ring

private theorem pointwise_kernel (c d : RealCharacterData) {F : G₂ → ℂ}
    (hF : F ∈ principalSeries ℝ 2 (realPositionCharacter [.character c, .character d]))
    (h : G₁) {k : G₂} (hk : k ∈ unitaryCompact ℝ 2) :
    determinantWeight c (1 / 2) k *
      ((χ d h⁻¹ * determinantWeight c (1 : ℂ) h) *
        (bump (rowSquare (rowPoint h.val k)) * normalizedOnRows c F (rowPoint h.val k))) =
      bump ((Matrix.GeneralLinearGroup.det h : ℝ) ^ 2) * F k := by
  let y : G₂ := Iwasawa.diagonalUnits (lowerDiagonal h)
  let w : G₂ →* ℂ := determinantWeight c (1 / 2)
  let C := principalSeriesCharacter ℝ 2
    (realPositionCharacter [.character c, .character d]) (lowerDiagonal h)
  have hY : F (y * k) = C * F k := by
    simpa only [OneMemClass.coe_one, mul_one] using hF.2 (lowerDiagonal h) 1 k
  have hW (g : G₂) : w g ≠ 0 := ((Group.isUnit g).map w).ne_zero
  have hNorm := (realGodementRowDescent 1 c [.character d] F hF).2 (y * k)
  rw [show lastRows (y * k).val = rowPoint h.val k from lastRows_lowerDiagonal h k] at hNorm
  simp only [Nat.cast_one] at hNorm
  change normalizedOnRows c F (rowPoint h.val k) = F (y * k) / w (y * k) at hNorm
  rw [hNorm, rowSquare_rowPoint h hk, hY, map_mul]
  change w k * ((χ d h⁻¹ * determinantWeight c (1 : ℂ) h) *
    (bump ((Matrix.GeneralLinearGroup.det h : ℝ) ^ 2) * (C * F k / (w y * w k)))) = _
  have hScalar : χ d h⁻¹ * determinantWeight c (1 : ℂ) h * C = w y :=
    lowerCharacter_cancel c d h
  field_simp [hW y, hW k]
  linear_combination ((bump ((Matrix.GeneralLinearGroup.det h : ℝ) ^ 2) : ℂ) * F k) * hScalar

private def lowerBump (h : G₁) : ℝ :=
  bump ((Matrix.GeneralLinearGroup.det h : ℝ) ^ 2)

private theorem continuous_lowerBump : Continuous lowerBump := by
  change Continuous (fun h : G₁ => bump (h.val.det ^ 2))
  have hVal : Continuous (Units.val : G₁ → Matrix (Fin 1) (Fin 1) ℝ) := Units.continuous_val
  exact (bump.contDiff (n := ⊤)).continuous.comp (hVal.matrix_det.pow 2)

private theorem hasCompactSupport_lowerBump : HasCompactSupport lowerBump := by
  have hK := isCompact_support_preimage (isCompact_singleton (x := (1 : G₂)))
    isCompact_shell (fun _ hx => fullRowRank_of_mem_shell hx)
  apply hK.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hK.isClosed
  intro h hh
  refine ⟨1, mem_singleton _, ?_⟩
  by_contra hx
  apply hh
  have heq := rowSquare_rowPoint h ((unitaryCompact ℝ 2).one_mem)
  simpa only [heq, lowerBump] using bump_rowSquare_eq_zero hx

section BumpIntegral

variable [MeasurableSpace G₁] [BorelSpace G₁] (μ : Measure G₁)
  [IsFiniteMeasureOnCompacts μ] [Measure.IsOpenPosMeasure μ]

private theorem integral_lowerBump_pos : 0 < ∫ h, lowerBump h ∂μ := by
  apply continuous_lowerBump.integral_pos_of_hasCompactSupport_nonneg_nonzero
    hasCompactSupport_lowerBump (fun _ => bump.nonneg) (x := (1 : G₁))
  have h : bump (1 : ℝ) = 1 := bump.one_of_mem_closedBall (mem_closedBall_self bump.rIn_pos.le)
  simp only [lowerBump, map_one, Units.val_one, one_pow, h]
  exact one_ne_zero

end BumpIntegral

/-- Every smooth real two-character `GL(2)` principal-series vector is one compactly
supported Godement section from the `GL(1)` character. -/
def RealGodementGLTwoGenerationStatement : Prop :=
  ∀ [MeasurableSpace G₁] [BorelSpace G₁] (μ : Measure G₁)
    [IsFiniteMeasureOnCompacts μ] [Measure.IsOpenPosMeasure μ]
    [Measure.IsMulRightInvariant μ] (c d : RealCharacterData) (F : G₂ → ℂ),
    F ∈ principalSeries ℝ 2 (realPositionCharacter [.character c, .character d]) →
      ∃ (S : Set X) (Φ : X → ℂ), IsCompact S ∧ (∀ x ∈ S, HasFullRowRank x) ∧
        ContDiff ℝ ∞ Φ ∧ (∀ x ∉ S, Φ x = 0) ∧ sectionValue μ c (χ d) Φ = F

theorem realGodementGLTwoGeneration : RealGodementGLTwoGenerationStatement := by
  intro _ _ μ _ _ _ c d F hF
  let Z : ℝ := ∫ h, lowerBump h ∂μ
  have hZ : 0 < Z := integral_lowerBump_pos μ
  let Φ : X → ℂ := fun x =>
    ((Z⁻¹ : ℝ) : ℂ) * (bump (rowSquare x) * normalizedOnRows c F x)
  have hΦZero (x : X) (hx : x ∉ shell) : Φ x = 0 := by
    simp only [Φ, bump_rowSquare_eq_zero hx, Complex.ofReal_zero, zero_mul, mul_zero]
  have hΦ : ContDiff ℝ ∞ Φ := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : HasFullRowRank x
    · have hB : ContDiff ℝ ∞ (fun x : X => (bump (rowSquare x) : ℂ)) :=
        Complex.ofRealCLM.contDiff.comp (bump.contDiff.comp contDiff_rowSquare)
      have hRow := (realGodementRowDescent 1 c [.character d] F hF).1.contDiffAt
        (isOpen_fullRowRank.mem_nhds hx)
      exact contDiffAt_const.mul (hB.contDiffAt.mul hRow)
    · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
      filter_upwards [isClosed_shell.isOpen_compl.mem_nhds
        (show x ∉ shell from fun h => hx (fullRowRank_of_mem_shell h))] with y hy
      exact hΦZero y hy
  have hSection := realGodementSection 1 μ c [.character d] (χ d)
    (RealRankOneStandardModule.characterVector_mem_standard d).1 shell isCompact_shell
    (fun _ hx => fullRowRank_of_mem_shell hx) Φ hΦ hΦZero
  have hK (k : G₂) (hk : k ∈ unitaryCompact ℝ 2) : sectionValue μ c (χ d) Φ k = F k := by
    calc
      _ = ∫ h : G₁, ((Z⁻¹ : ℝ) : ℂ) * (lowerBump h * F k) ∂μ := by
        unfold sectionValue innerIntegral
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with h
        change determinantWeight c (((1 : ℕ) : ℂ) / 2) k *
          ((χ d h⁻¹ * determinantWeight c ((((1 : ℕ) : ℂ) + 1) / 2) h) *
            (((Z⁻¹ : ℝ) : ℂ) * (bump (rowSquare (rowPoint h.val k)) *
              normalizedOnRows c F (rowPoint h.val k)))) = _
        rw [show ((((1 : ℕ) : ℂ) + 1) / 2) = 1 by norm_num, Nat.cast_one]
        simp only [lowerBump]
        linear_combination ((Z⁻¹ : ℝ) : ℂ) * pointwise_kernel c d hF h hk
      _ = F k := by
        rw [integral_const_mul, integral_mul_const, integral_complex_ofReal]
        change ((Z⁻¹ : ℝ) : ℂ) * ((Z : ℂ) * F k) = F k
        rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hZ.ne',
          Complex.ofReal_one, one_mul]
  refine ⟨shell, Φ, isCompact_shell, fun _ hx => fullRowRank_of_mem_shell hx, hΦ, hΦZero, ?_⟩
  funext g
  obtain ⟨a, u, k, hk, rfl⟩ := exists_diagonalUnits_mul_upperUnipotent_mul_unitaryCompact g
  rw [hSection.2 a u k, hF.2 a u k, hK k hk]

end GLTwo

end Langlands.Global.RankinSelbergGlobal.RealGodement
