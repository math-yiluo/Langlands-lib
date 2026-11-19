import Langlands.Global.RankinSelberg.RealGodementRowCompletion
import Langlands.Global.RankinSelberg.RealGodementSection
import Langlands.Representation.Archimedean.RealStrictCharacterLanglandsQuotient

/-! # Descent of normalized real position principal-series vectors to bottom rows -/

noncomputable section

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open scoped Matrix.Norms.Operator Manifold ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

variable {m : ℕ}

local notation "X" => Matrix (Fin m) (Fin (m + 1)) ℝ
local notation "Y" => Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ
local notation "G" => Langlands.GeneralLinear (m + 1) ℝ

private theorem lastRows_mul (A B : Y) : lastRows (A * B) = lastRows A * B := rfl

theorem hasFullRowRank_lastRows (g : G) : HasFullRowRank (lastRows g.val) := by
  refine ⟨(g⁻¹).val.submatrix id Fin.succ, ?_⟩
  ext i j
  have h := congrArg (fun a : Y => a i.succ j.succ) g.mul_inv
  simpa [Matrix.mul_apply, Matrix.one_apply, Matrix.submatrix, lastRows] using h

private def leadingDiagonal (b : G) : Fin (m + 1) → ℝˣ :=
  Fin.cases (Matrix.GeneralLinearGroup.det b) (fun _ => 1)

private theorem exists_unipotent_of_lastRows_eq_one (b : G)
    (h : lastRows b.val = lastRows (1 : Y)) :
    ∃ u : upperUnipotent (m + 1) ℝ, b = Iwasawa.diagonalUnits (leadingDiagonal b) * u.val := by
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
  have hDiag (i : Fin (m + 1)) : b.val i i = (d i : ℝ) := by
    induction i using Fin.cases with
    | zero => exact hDet.symm
    | succ i => rw [hRow, Matrix.one_apply_eq]; rfl
  let u₀ : G := (Iwasawa.diagonalUnits d)⁻¹ * b
  have hEntry (i j : Fin (m + 1)) :
      u₀.val i j = (d i : ℝ)⁻¹ * b.val i j := by
    simp only [u₀, ← map_inv, Units.val_mul, Iwasawa.diagonalUnits_val,
      Matrix.diagonal_mul, Pi.inv_apply, Units.val_inv_eq_inv_val]
  have hu : u₀ ∈ upperUnipotent (m + 1) ℝ := by
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · rw [hEntry, hb hij, mul_zero]
    · rw [hEntry, hDiag, inv_mul_cancel₀ (d i).ne_zero]
  refine ⟨⟨u₀, hu⟩, ?_⟩
  change b = Iwasawa.diagonalUnits d * ((Iwasawa.diagonalUnits d)⁻¹ * b)
  rw [← mul_assoc, mul_inv_cancel, one_mul]

private theorem principalSeriesCharacter_leading (c : RealCharacterData) (ds : List RealBlock)
    (b : G) :
    principalSeriesCharacter ℝ (m + 1) (realPositionCharacter (.character c :: ds))
      (leadingDiagonal b) = determinantWeight c ((m : ℂ) / 2) b := by
  simp only [principalSeriesCharacter, Fin.prod_univ_succ, realPositionCharacter,
    leadingDiagonal, Fin.cases_zero, Fin.cases_succ, Real.norm_eq_abs,
    Module.finrank_self, pow_one, Fin.val_zero, Nat.cast_zero, sub_zero,
    Nat.cast_succ, add_sub_cancel_right, RealStrictCharacterLanglandsQuotient.realPositionCharacter_one,
    Units.val_one, abs_one, Complex.ofReal_one, Complex.one_cpow, mul_one, Finset.prod_const_one]
  rfl

private theorem determinantWeight_ne_zero' (c : RealCharacterData) (z : ℂ) (g : G) :
    determinantWeight c z g ≠ 0 := by
  have h := (map_mul (determinantWeight c z) g g⁻¹).symm
  rw [mul_inv_cancel, map_one] at h
  exact left_ne_zero_of_mul (h.trans_ne one_ne_zero)

private theorem normalized_eq_of_lastRows_eq (c : RealCharacterData) (ds : List RealBlock)
    {f : G → ℂ}
    (hf : f ∈ principalSeries ℝ (m + 1) (realPositionCharacter (.character c :: ds)))
    {g h : G} (hRows : lastRows g.val = lastRows h.val) :
    f g / determinantWeight c ((m : ℂ) / 2) g =
      f h / determinantWeight c ((m : ℂ) / 2) h := by
  let w : G →* ℂ := determinantWeight c ((m : ℂ) / 2)
  let b := g * h⁻¹
  have hb : lastRows b.val = lastRows (1 : Y) := by
    change lastRows (g * h⁻¹).val = lastRows (1 : Y)
    rw [Units.val_mul, lastRows_mul, hRows, ← lastRows_mul, ← Units.val_mul,
      mul_inv_cancel, Units.val_one]
  obtain ⟨u, hu⟩ := exists_unipotent_of_lastRows_eq_one b hb
  have hg : b * h = g := by simp [b]
  have hF : f g = w b * f h := by
    rw [← hg, hu]
    rw [hf.2 (leadingDiagonal b) u h, principalSeriesCharacter_leading]
    rw [← hu]
  have hW : w g = w b * w h := (congrArg w hg).symm.trans (map_mul w b h)
  change f g / w g = f h / w h
  apply (div_eq_div_iff (show w g ≠ 0 from determinantWeight_ne_zero' c _ g)
    (show w h ≠ 0 from determinantWeight_ne_zero' c _ h)).2
  rw [hF, hW]
  ring

/-- The upper vector divided by its leading determinant factor, in bottom-row coordinates. -/
def normalizedOnRows (c : RealCharacterData) (f : G → ℂ) (x : X) : ℂ :=
  unitsExtension f (completionMatrix x) /
    ((completionMatrix x).det : ℂ) ^ (c.exponent + (m : ℂ) / 2)

private theorem normalizedOnRows_eq_completeRows (c : RealCharacterData) (f : G → ℂ)
    (x : X) (hx : HasFullRowRank x) :
    normalizedOnRows c f x = f (completeRows x hx) /
      determinantWeight c ((m : ℂ) / 2) (completeRows x hx) := by
  let g := completeRows x hx
  have hg : g.val = completionMatrix x := completeRows_val x hx
  have hdet : 0 < (Matrix.GeneralLinearGroup.det g : ℝ) := by
    change 0 < g.val.det
    rw [hg]
    exact det_completionMatrix_pos hx
  have hp : ((Matrix.GeneralLinearGroup.det g : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hdet.ne'
  have hw : determinantWeight c ((m : ℂ) / 2) g =
      ((g.val.det : ℝ) : ℂ) ^ (c.exponent + (m : ℂ) / 2) := by
    change (c.character (Matrix.GeneralLinearGroup.det g) : ℂ) *
      ((|(Matrix.GeneralLinearGroup.det g : ℝ)| : ℝ) : ℂ) ^ ((m : ℂ) / 2) = _
    rw [c.character_eq, abs_of_pos hdet, div_self hdet.ne', Complex.ofReal_one, one_pow,
      one_mul, ← Complex.cpow_add _ _ hp]
    rfl
  change normalizedOnRows c f x = f g / determinantWeight c ((m : ℂ) / 2) g
  rw [normalizedOnRows, ← hg, unitsExtension_val, hw]

/-- The normalized upper principal-series vector is a smooth rectangular function on
the full-row-rank domain, and pulling it back gives the original normalized values. -/
def RealGodementRowDescentStatement : Prop :=
  ∀ (m : ℕ) (c : RealCharacterData) (ds : List RealBlock)
    (f : Langlands.GeneralLinear (m + 1) ℝ → ℂ),
    f ∈ principalSeries ℝ (m + 1) (realPositionCharacter (.character c :: ds)) →
      ContDiffOn ℝ ∞ (normalizedOnRows c f) {x | HasFullRowRank x} ∧
      ∀ g : Langlands.GeneralLinear (m + 1) ℝ,
        normalizedOnRows c f (lastRows g.val) =
          f g / determinantWeight c ((m : ℂ) / 2) g

theorem realGodementRowDescent : RealGodementRowDescentStatement := by
  intro m c ds f hf
  constructor
  · have hNumerator : ContDiffOn ℝ ∞ (fun x => unitsExtension f (completionMatrix x))
        {x | HasFullRowRank x} := (contDiffOn_unitsExtension hf.1).comp
      contDiff_completionMatrix.contDiffOn
      (fun x hx => (hasFullRowRank_iff_isUnit_completion x).1 hx)
    have hDet : ContDiff ℝ ∞
        (Matrix.det : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ → ℝ) :=
      PrincipalSeriesExtension.contDiff_det_comp PrincipalSeriesExtension.contDiff_entry
    have hDenominator : ContDiffOn ℝ ∞
        (fun x : Matrix (Fin m) (Fin (m + 1)) ℝ =>
          ((completionMatrix x).det : ℂ) ^ (c.exponent + (m : ℂ) / 2))
        {x | HasFullRowRank x} := by
      intro x hx
      have hd := PrincipalSeriesExtension.contDiffAt_ofReal_cpow hDet.contDiffAt
        (det_completionMatrix_pos hx) (c.exponent + (m : ℂ) / 2)
      exact (hd.comp x contDiff_completionMatrix.contDiffAt).contDiffWithinAt
    change ContDiffOn ℝ ∞ (fun x : Matrix (Fin m) (Fin (m + 1)) ℝ =>
      unitsExtension f (completionMatrix x) /
        ((completionMatrix x).det : ℂ) ^ (c.exponent + (m : ℂ) / 2)) {x | HasFullRowRank x}
    have hInv := hDenominator.fun_inv (fun x hx => Complex.cpow_ne_zero_iff.mpr
      (Or.inl (Complex.ofReal_ne_zero.mpr (det_completionMatrix_pos hx).ne')))
    simpa only [div_eq_mul_inv] using hNumerator.mul hInv
  · intro g
    have hx := hasFullRowRank_lastRows g
    rw [normalizedOnRows_eq_completeRows c f _ hx]
    exact normalized_eq_of_lastRows_eq c ds hf (lastRows_completeRows _ hx)

end Langlands.Global.RankinSelbergGlobal.RealGodement
