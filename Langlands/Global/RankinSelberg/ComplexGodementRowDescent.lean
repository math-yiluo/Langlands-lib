import Langlands.Global.RankinSelberg.ComplexGodementRowCompletion
import Langlands.Global.RankinSelberg.ComplexGodementSection
import Langlands.Representation.Archimedean.ComplexStrictLanglandsQuotient
import Langlands.Representation.Archimedean.ComplexPrincipalSeriesExtension

/-! # Descent of normalized complex position principal-series vectors to bottom rows -/

noncomputable section

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open scoped Matrix.Norms.Operator Manifold ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodement

variable {m : ℕ}

local notation "X" => Matrix (Fin m) (Fin (m + 1)) ℂ
local notation "Y" => Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ
local notation "G" => Langlands.GeneralLinear (m + 1) ℂ

private theorem trailingRows_mul (A B : Y) : trailingRows (A * B) = trailingRows A * B := rfl

theorem hasFullRowRank_trailingRows (g : G) : HasFullRowRank (trailingRows g.val) := by
  refine ⟨(g⁻¹).val.submatrix id Fin.succ, ?_⟩
  ext i j
  have h := congrArg (fun a : Y => a i.succ j.succ) g.mul_inv
  simpa [Matrix.mul_apply, Matrix.one_apply, Matrix.submatrix, trailingRows] using h

private def leadingDiagonal (b : G) : Fin (m + 1) → ℂˣ :=
  Fin.cases (Matrix.GeneralLinearGroup.det b) (fun _ => 1)

private theorem exists_unipotent_of_trailingRows_eq_one (b : G)
    (h : trailingRows b.val = trailingRows (1 : Y)) :
    ∃ u : upperUnipotent (m + 1) ℂ, b = Iwasawa.diagonalUnits (leadingDiagonal b) * u.val := by
  have hRow (i : Fin m) (j : Fin (m + 1)) :
      b.val i.succ j = (1 : Y) i.succ j :=
    congrArg (fun x : X => x i j) h
  have hb : b.val.IsUpperTriangular := by
    intro i j
    induction i using Fin.cases with
    | zero => exact fun hi => (Fin.not_lt_zero _ hi).elim
    | succ i =>
      intro hi
      rw [hRow i j]
      exact Matrix.one_apply_ne (ne_of_gt (show j < i.succ from hi))
  have hDet : b.val.det = b.val 0 0 := by
    rw [Matrix.det_of_isUpperTriangular hb, Fin.prod_univ_succ]
    simp only [hRow, Matrix.one_apply_eq, Finset.prod_const_one, mul_one]
  let d := leadingDiagonal b
  have hDiag (i : Fin (m + 1)) : b.val i i = (d i : ℂ) := by
    induction i using Fin.cases with
    | zero => exact hDet.symm
    | succ i => rw [hRow, Matrix.one_apply_eq]; rfl
  let u₀ : G := (Iwasawa.diagonalUnits d)⁻¹ * b
  have hEntry (i j : Fin (m + 1)) :
      u₀.val i j = (d i : ℂ)⁻¹ * b.val i j := by
    simp only [u₀, ← map_inv, Units.val_mul, Iwasawa.diagonalUnits_val,
      Matrix.diagonal_mul, Pi.inv_apply, Units.val_inv_eq_inv_val]
  have hu : u₀ ∈ upperUnipotent (m + 1) ℂ := by
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · rw [hEntry, hb hij, mul_zero]
    · rw [hEntry, hDiag, inv_mul_cancel₀ (d i).ne_zero]
  refine ⟨⟨u₀, hu⟩, ?_⟩
  change b = Iwasawa.diagonalUnits d * ((Iwasawa.diagonalUnits d)⁻¹ * b)
  rw [← mul_assoc, mul_inv_cancel, one_mul]

private theorem principalSeriesCharacter_leading (c : ComplexCharacterData)
    (ds : List ComplexCharacterData) (b : G) :
    principalSeriesCharacter ℂ (m + 1) (complexPositionCharacter (c :: ds))
      (leadingDiagonal b) = characterWeight c ((m : ℂ) / 2) (determinant b) := by
  have h : (((m + 1 : ℕ) : ℂ) - 1) / 2 - ((0 : ℕ) : ℂ) = (m : ℂ) / 2 := by
    push_cast
    ring
  simp only [principalSeriesCharacter, Fin.prod_univ_succ, leadingDiagonal, Fin.cases_zero,
    Fin.cases_succ, Fin.val_zero, Complex.finrank_real_complex, h,
    ComplexStrictLanglandsQuotient.complexPositionCharacter_one, Units.val_one, norm_one,
    one_pow, Complex.ofReal_one, Complex.one_cpow, mul_one, Finset.prod_const_one]
  rfl

private theorem normalized_eq_of_trailingRows_eq (c : ComplexCharacterData)
    (ds : List ComplexCharacterData) {f : G → ℂ}
    (hf : f ∈ complexStandardModule (m + 1) (c :: ds))
    {g h : G} (hRows : trailingRows g.val = trailingRows h.val) :
    f g / characterWeight c ((m : ℂ) / 2) (determinant g) =
      f h / characterWeight c ((m : ℂ) / 2) (determinant h) := by
  let w : G →* ℂ := (characterWeight c ((m : ℂ) / 2)).comp (determinant : G →* ℂˣ)
  let b := g * h⁻¹
  have hb : trailingRows b.val = trailingRows (1 : Y) := by
    change trailingRows (g * h⁻¹).val = trailingRows (1 : Y)
    rw [Units.val_mul, trailingRows_mul, hRows, ← trailingRows_mul, ← Units.val_mul,
      mul_inv_cancel, Units.val_one]
  obtain ⟨u, hu⟩ := exists_unipotent_of_trailingRows_eq_one b hb
  have hg : b * h = g := by simp [b]
  have hF : f g = w b * f h := by
    rw [← hg, hu, hf.2 (leadingDiagonal b) u h, principalSeriesCharacter_leading, ← hu]
    rfl
  have hW : w g = w b * w h := (congrArg w hg).symm.trans (map_mul w b h)
  change f g / w g = f h / w h
  have w_ne_zero (v : G) : w v ≠ 0 := ((Group.isUnit v).map w).ne_zero
  apply (div_eq_div_iff (w_ne_zero g) (w_ne_zero h)).2
  rw [hF, hW]
  ring

private def positiveWeight (c : ComplexCharacterData) (s : ℂ) (t : ℝ) : ℂ :=
  (t : ℂ) ^ (2 * c.exponent) * ((t ^ 2 : ℝ) : ℂ) ^ s

private theorem positiveWeight_eq (c : ComplexCharacterData) (s : ℂ) (z : ℂˣ)
    (hr : (((z : ℂ).re : ℝ) : ℂ) = (z : ℂ)) (hpos : 0 < (z : ℂ).re) :
    positiveWeight c s (z : ℂ).re = characterWeight c s z := by
  unfold positiveWeight
  simp only [characterWeight, normPower, MonoidHom.coe_mk, OneHom.coe_mk,
    ComplexMaximalParabolicIntegration.normSqC, c.character_eq]
  have hnorm : ‖(z : ℂ)‖ = (z : ℂ).re := by
    conv_lhs => rw [← hr]
    rw [Complex.norm_real, Real.norm_of_nonneg hpos.le]
  rw [hnorm, hr, div_self z.ne_zero, one_zpow, one_mul]

/-- The upper vector divided by its leading determinant factor, in bottom-row coordinates. -/
def normalizedOnRows (c : ComplexCharacterData) (f : G → ℂ) (x : X) : ℂ :=
  unitsExtension f (completionMatrix x) /
    positiveWeight c ((m : ℂ) / 2) (completionMatrix x).det.re

private theorem normalizedOnRows_eq_completeRows (c : ComplexCharacterData)
    (f : G → ℂ) (x : X) (hx : HasFullRowRank x) :
    normalizedOnRows c f x = f (completeRows x hx) /
      characterWeight c ((m : ℂ) / 2) (determinant (completeRows x hx)) := by
  let g := completeRows x hx
  have hg : g.val = completionMatrix x := completeRows_val x hx
  have hpos : 0 < (determinant g : ℂ).re := by
    change 0 < g.val.det.re
    rw [hg]
    exact det_completionMatrix_pos hx
  have hreal : ((determinant g : ℂ).re : ℂ) = (determinant g : ℂ) := by
    change (g.val.det.re : ℂ) = g.val.det
    rw [hg, det_completionMatrix_ofReal_re]
  change normalizedOnRows c f x = f g / _
  unfold normalizedOnRows
  rw [← hg, unitsExtension_val]
  rw [show g.val.det = (determinant g : ℂ) from rfl, positiveWeight_eq c _ _ hreal hpos]

/-- The normalized upper principal-series vector is smooth in bottom-row coordinates. -/
theorem contDiffOn_normalizedOnRows (c : ComplexCharacterData) (ds : List ComplexCharacterData)
    {f : G → ℂ} (hf : f ∈ complexStandardModule (m + 1) (c :: ds)) :
    ContDiffOn ℝ ∞ (normalizedOnRows c f) {x | HasFullRowRank x} := by
  have hNumerator : ContDiffOn ℝ ∞ (fun x : X => unitsExtension f (completionMatrix x))
      {x | HasFullRowRank x} := (contDiffOn_unitsExtension hf.1).comp
    contDiff_completionMatrix.contDiffOn (fun x hx => (hasFullRowRank_iff_isUnit_completion x).1 hx)
  have hDet : ContDiff ℝ ∞ (fun x : X => (completionMatrix x).det.re) :=
    Complex.reCLM.contDiff.comp (ComplexMaximalParabolicIntegration.contDiff_det.comp
      contDiff_completionMatrix)
  have hDenominator : ContDiffOn ℝ ∞
      (fun x : X => positiveWeight c ((m : ℂ) / 2) (completionMatrix x).det.re)
      {x | HasFullRowRank x} := by
    intro x hx
    have hpos := det_completionMatrix_pos hx
    exact ((ComplexPrincipalSeriesExtension.contDiffAt_ofReal_cpow hDet.contDiffAt hpos _).mul
      (ComplexPrincipalSeriesExtension.contDiffAt_ofReal_cpow (hDet.pow 2).contDiffAt
        (pow_pos hpos 2) _)).contDiffWithinAt
  have hInv := hDenominator.fun_inv (fun x hx => by
    have ht := det_completionMatrix_pos hx
    refine mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl
      (Complex.ofReal_ne_zero.mpr ht.ne'))) (Complex.cpow_ne_zero_iff.mpr (Or.inl
      (Complex.ofReal_ne_zero.mpr (pow_pos ht 2).ne'))))
  change ContDiffOn ℝ ∞ (fun x : X => unitsExtension f (completionMatrix x) /
    positiveWeight c ((m : ℂ) / 2) (completionMatrix x).det.re) {x | HasFullRowRank x}
  simpa only [div_eq_mul_inv] using hNumerator.mul hInv

/-- Pulling the rectangular function back to the group gives the normalized vector. -/
theorem normalizedOnRows_trailingRows (c : ComplexCharacterData) (ds : List ComplexCharacterData)
    {f : G → ℂ} (hf : f ∈ complexStandardModule (m + 1) (c :: ds)) (g : G) :
    normalizedOnRows c f (trailingRows g.val) =
      f g / characterWeight c ((m : ℂ) / 2) (determinant g) := by
  have hx := hasFullRowRank_trailingRows g
  rw [normalizedOnRows_eq_completeRows c f _ hx]
  exact normalized_eq_of_trailingRows_eq c ds hf (trailingRows_completeRows _ hx)

end Langlands.Global.RankinSelbergGlobal.ComplexGodement
