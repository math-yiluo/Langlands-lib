import Langlands.Global.Factors.CuspidalPairEisensteinOpenCellSliceBound
import Langlands.Global.Factors.CuspidalPairEisensteinOpenCellDeterminant
import Langlands.Global.Factors.CuspidalPairEisensteinPartialOpenCell
import Langlands.Group.GL.BlockDeterminant
import Langlands.Topology.CompactNormCharacter

/-! # A pointwise majorant for the open-cell integrand

For `g = w u'(Y) = p k` with Levi part `m = diag(m₁, m₂)` of `p`, the determinant `det g` and
`det k` have norm one, so `|det m₁| |det m₂| = 1`. With `X = |det m₂|` the Levi Whittaker bound
`|δ_P(m)^(1/2 + s/N)| · C |det m₁|^(β₁) |det m₂|^(β₂)` (`N = r + t + 2`) equals
`C X^(-(Re s + N/2 + β₁ - β₂))`. When `e = Re s + N/2 + β₁ - β₂ ≥ 0`, the determinant bound
(which needs `e ≥ 0`) turns it into a constant times the majorant `Ω_e(Y)`. See the paired
Markdown. -/

noncomputable section

set_option autoImplicit false

universe u

open NumberField
open scoped NNReal
open Langlands.Automorphic (CuspidalOperatorRealization)

namespace Langlands.Global.CuspidalPairEisenstein.OpenCellPointwise

open Langlands.GeneralLinear AdelicBlockParabolic AdelicBlockDeterminantCharacter
  PrimitiveAdelicHeight Oneplace OpenCellBound OpenCellDeterminant OpenCellMajorant

variable {F : Type u} [Field F] [NumberField F] {r t : ℕ}

section Determinants

theorem absDet_one (n : ℕ) : absDet F n 1 = 1 := by
  simp [absDet]

theorem absDet_pow {n : ℕ} (g : AdelicGL F n) (k : ℕ) : absDet F n (g ^ k) = absDet F n g ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, absDet_one]
  | succ k ih => rw [pow_succ, absDet_mul, ih, pow_succ]

/-- `w` is a permutation matrix, so `|det w| = 1`. -/
theorem absDet_openCellWeyl : absDet F (r + t + 2) (openCellWeyl F r t) = 1 := by
  set σ := Shahidi.blockWeylPermutation (r + 1) (t + 1)
  have hk : openCellWeyl F r t ^ orderOf σ = 1 := by
    change (GeneralLinear.reindex (finCongr (by omega : r + 1 + (t + 1) = r + t + 2))
      (GeneralLinear.permutation (r + 1 + (t + 1)) (Adeles F) σ)) ^ orderOf σ = 1
    rw [← map_pow, ← map_pow, pow_orderOf_eq_one, map_one, map_one]
  have hpow : absDet F (r + t + 2) (openCellWeyl F r t) ^ orderOf σ = 1 := by
    rw [← absDet_pow, hk, absDet_one]
  exact (pow_eq_one_iff_of_nonneg (absDet_pos F _ _).le (orderOf_pos σ).ne').mp hpow

theorem det_val_reindex {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {R : Type*} [CommRing R] (e : ι ≃ κ) (g : Matrix.GeneralLinearGroup ι R) :
    ((GeneralLinear.reindex e g : Matrix.GeneralLinearGroup κ R) : Matrix κ κ R).det =
      (g : Matrix ι ι R).det :=
  Matrix.det_reindex_self e g.val

/-- `u'(Y)` is unipotent, so `det u'(Y) = 1`. -/
theorem det_openCellUnipotent (Y : Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)) :
    ((openCellUnipotent F r t Y : AdelicGL F (r + t + 2)) :
      Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) (Adeles F)).det = 1 := by
  have h1 : ((openCellUnipotent F r t Y : AdelicGL F (r + t + 2)) :
      Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) (Adeles F)).det =
      ((Shahidi.intertwiningUnipotent (r + 1) (t + 1) (Adeles F) Y :
        Langlands.GeneralLinear (r + 1 + (t + 1)) (Adeles F)) :
          Matrix (Fin (r + 1 + (t + 1))) (Fin (r + 1 + (t + 1))) (Adeles F)).det :=
    det_val_reindex _ _
  have h2 : ((Shahidi.intertwiningUnipotent (r + 1) (t + 1) (Adeles F) Y :
        Langlands.GeneralLinear (r + 1 + (t + 1)) (Adeles F)) :
          Matrix (Fin (r + 1 + (t + 1))) (Fin (r + 1 + (t + 1))) (Adeles F)).det =
      ((Shahidi.upper (t + 1) (r + 1) (Adeles F) Y :
        Langlands.GeneralLinear (t + 1 + (r + 1)) (Adeles F)) :
          Matrix (Fin (t + 1 + (r + 1))) (Fin (t + 1 + (r + 1))) (Adeles F)).det :=
    det_val_reindex _ _
  have h3 : ((Shahidi.upper (t + 1) (r + 1) (Adeles F) Y :
        Langlands.GeneralLinear (t + 1 + (r + 1)) (Adeles F)) :
          Matrix (Fin (t + 1 + (r + 1))) (Fin (t + 1 + (r + 1))) (Adeles F)).det =
      (Matrix.fromBlocks (1 : Matrix (Fin (t + 1)) (Fin (t + 1)) (Adeles F)) Y 0 1).det :=
    det_val_reindex _ _
  rw [h1, h2, h3]
  rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, Matrix.det_one, mul_one]

theorem absDet_eq_one_of_det_eq_one {n : ℕ} {g : AdelicGL F n}
    (hg : (g : Matrix (Fin n) (Fin n) (Adeles F)).det = 1) : absDet F n g = 1 := by
  have h : AdelicGL.determinant F n g = 1 := Units.ext hg
  rw [absDet, h, map_one, Units.val_one, NNReal.coe_one]

theorem absDet_openCellUnipotent (Y : Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)) :
    absDet F (r + t + 2) (openCellUnipotent F r t Y) = 1 :=
  absDet_eq_one_of_det_eq_one (det_openCellUnipotent Y)

theorem absDet_of_mem_standardCompact {n : ℕ} {k : AdelicGL F n}
    (hk : k ∈ standardCompact F n) : absDet F n k = 1 := by
  have h := RankinSelberg.LastRowReduction.eq_one_of_isCompact (determinantNorm F n).toMonoidHom (determinantNorm F n).continuous
    (standardCompact F n) (isCompact_standardCompact F n) hk
  change ((determinantNorm F n k : ℝ≥0) : ℝ) = 1
  rw [show determinantNorm F n k = 1 from h, Units.val_one, NNReal.coe_one]

/-- The determinant of a parabolic element is the product of the determinants of its blocks. -/
theorem absDet_parabolic (p : Full F (blockShape r t)) :
    absDet F (r + t + 2) p.val =
      absDet F (r + 1) (leviFst ((blockShape r t).leviProjection (Adeles F) p)) *
        absDet F (t + 1) (leviSnd ((blockShape r t).leviProjection (Adeles F) p)) := by
  have h := determinant_blockParabolic (blockShape r t) p
  have h2 : absDet F (r + t + 2) p.val =
      ∏ i, absDet F ((blockShape r t).size i) ((blockShape r t).leviProjection (Adeles F) p i) := by
    change ((IdeleAbsoluteValue.full F (GeneralLinear.determinant p.val) : ℝ≥0) : ℝ) = _
    rw [h, map_prod, Units.coe_prod, NNReal.coe_prod]
    rfl
  rw [h2, CuspidalPairEisenstein.prod_blocks]
  rfl

/-- On the open cell: if `p k = w u'(Y)` with `k` in the standard maximal compact subgroup, then
`|det m₁| |det m₂| = 1`. -/
theorem absDet_leviFst_mul_leviSnd {p : Full F (blockShape r t)} {k : AdelicGL F (r + t + 2)}
    {Y : Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)}
    (hk : k ∈ standardCompact F (r + t + 2))
    (hpk : p.val * k = openCellWeyl F r t * openCellUnipotent F r t Y) :
    absDet F (r + 1) (leviFst ((blockShape r t).leviProjection (Adeles F) p)) *
      absDet F (t + 1) (leviSnd ((blockShape r t).leviProjection (Adeles F) p)) = 1 := by
  have h := congrArg (absDet F (r + t + 2)) hpk
  rw [absDet_mul, absDet_mul, absDet_of_mem_standardCompact hk, absDet_openCellWeyl,
    absDet_openCellUnipotent, mul_one, mul_one] at h
  rw [← absDet_parabolic, h]

end Determinants

section Exponent

/-- With `|det m₁| |det m₂| = 1` and `X = |det m₂|`,
`|δ_P(m)^(1/2 + s/N)| |det m₁|^(β₁) |det m₂|^(β₂) = X^(-(Re s + N/2 + β₁ - β₂))`. -/
theorem norm_levFactor_mul_pairWeight (s : ℂ) (β₁ β₂ : ℝ) (m : FullLevi F (blockShape r t))
    (hdet : absDet F (r + 1) (leviFst m) * absDet F (t + 1) (leviSnd m) = 1) :
    ‖levFactor s m‖ * pairWeight r t β₁ β₂ m =
      absDet F (t + 1) (leviSnd m) ^ (-(s.re + ((r + t + 2 : ℕ) : ℝ) / 2 + β₁ - β₂)) := by
  set X := absDet F (t + 1) (leviSnd m) with hXdef
  have hX : 0 < X := absDet_pos F _ _
  set L := Real.log X with hL
  have hXL : X = Real.exp L := (Real.exp_log hX).symm
  have ha : absDet F (r + 1) (leviFst m) = Real.exp (-L) := by
    rw [Real.exp_neg, ← hXL]
    exact eq_inv_of_mul_eq_one_left hdet
  set N : ℝ := ((r + t + 2 : ℕ) : ℝ) with hN
  have hNpos : 0 < N := by positivity
  have hδ : ((leviCharacter F (blockShape r t) m : ℝ≥0) : ℝ) = Real.exp (-(N * L)) := by
    have hm : leviOf (leviFst m) (leviSnd m) = m :=
      (Shahidi.twoBlockLeviEquiv (Nat.succ_pos r) (Nat.succ_pos t) (Adeles F)).symm_apply_apply m
    have h := leviCharacter_leviOf (leviFst m) (leviSnd m)
    rw [hm] at h
    rw [h, Units.val_div_eq_div_val, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val,
      NNReal.coe_div, NNReal.coe_pow, NNReal.coe_pow]
    change absDet F (r + 1) (leviFst m) ^ (t + 1) / X ^ (r + 1) = _
    rw [ha, hXL, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_sub]
    congr 1
    rw [hN]
    push_cast
    ring
  have hlev : ‖levFactor s m‖ = Real.exp (-(N * L) / 2) * Real.exp (-(s.re * L)) := by
    rw [levFactor, norm_mul, coe_leviHalfCharacter, Complex.norm_real, Real.norm_eq_abs,
      Real.coe_sqrt, hδ, ← Real.exp_half, abs_of_pos (Real.exp_pos _), Complex.norm_exp,
      Real.log_exp]
    congr 2
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
      Complex.div_natCast_re]
    rw [hN]
    field_simp
  have hw : pairWeight r t β₁ β₂ m = Real.exp (-L * β₁) * Real.exp (L * β₂) := by
    rw [pairWeight, ha, ← hXdef, hXL, ← Real.exp_mul, ← Real.exp_mul]
  rw [hlev, hw, hXL, ← Real.exp_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

end Exponent

section Bound

variable [CompactSpace (AdeleQuotient F)]
  {T : CuspidalOperatorRealization F r} {T' : CuspidalOperatorRealization F t}
  {φ : AdelicGL F (r + t + 2) → ℂ}

/-- **Pointwise majorant.** For a standard additive character `ψ` and a cuspidal-pair section
`φ` there is a real `b` such that for every `s` with `Re s + b ≥ 0` the open-cell integrand is
bounded by a constant times the majorant `Ω_(Re s + b)`. -/
theorem exists_norm_openCellIntegrand_le (ψ : AddChar (Adeles F) ℂ)
    (hψ : RankinSelbergGlobal.IsStandardAdditiveCharacter F ψ) (hφ : IsSection T T' φ) :
    ∃ b : ℝ, ∀ s : ℂ, 0 ≤ s.re + b → ∃ C : ℝ, 0 ≤ C ∧
      ∀ Y, ‖openCellIntegrand ψ φ s Y‖ ≤ C * majorant (s.re + b) Y := by
  obtain ⟨β₁, β₂, C, hC, hb⟩ := exists_slice_bound hφ
  refine ⟨((r + t + 2 : ℕ) : ℝ) / 2 + β₁ - β₂, fun s hs => ?_⟩
  set e := s.re + (((r + t + 2 : ℕ) : ℝ) / 2 + β₁ - β₂) with he
  refine ⟨C * ((((t + 2).factorial : ℝ) ^ Module.finrank ℚ F) ^ e * 2 ^ e),
    mul_nonneg hC (by positivity), fun Y => ?_⟩
  obtain ⟨p, k, hk, hpk⟩ := exists_parabolic_factor' F r t
    (openCellWeyl F r t * openCellUnipotent F r t Y)
  have hψ1 : ∀ a : Adeles F, ‖ψ a‖ = 1 := hψ.2.2.2
  rw [openCellIntegrand, norm_mul, Complex.norm_conj, hψ1, mul_one]
  have hW := norm_leviWhittaker_le ψ hψ hφ hb s p ⟨k, hk⟩
  change ‖leviWhittaker F r t ψ (twisted φ s) (p.val * k)‖ ≤ _ at hW
  rw [hpk] at hW
  change ‖leviWhittaker F r t ψ (twisted φ s) _‖ ≤ _
  refine hW.trans ?_
  have hdet := absDet_leviFst_mul_leviSnd hk hpk
  rw [mul_left_comm, norm_levFactor_mul_pairWeight s β₁ β₂ _ hdet, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hC
  have h := rpow_neg_absDet_le_majorant hk hpk hs
  rw [he] at h ⊢
  convert h using 2
  ring

end Bound

end Langlands.Global.CuspidalPairEisenstein.OpenCellPointwise
