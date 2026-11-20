import Langlands.Global.RankinSelberg.RealGodementGramCutoff
import Langlands.Global.RankinSelberg.RealGodementLowerCutoff

/-! # Localization of the compact real Godement kernel -/

noncomputable section

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open GramFormula PrincipalSeriesExtension RealBlockPosition RealJacquetFrobenius
open Set
open scoped Matrix.Norms.Operator ContDiff Manifold

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

variable {m : ℕ}

local notation "M" => Matrix (Fin m) (Fin m) ℝ
local notation "Y" => Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ
local notation "G" => Langlands.GeneralLinear m ℝ
local notation "H" => Langlands.GeneralLinear (m + 1) ℝ

private theorem lowerBlock_entries (h : G) : (lowerBlock h).val =
    (Fin.cases (Fin.cases 1 fun _ => 0) (fun i => Fin.cases 0 (h.val i)) : Y) :=
  IsUnit.unit_spec _

theorem continuous_lowerBlock : Continuous (lowerBlock : G → H) := by
  apply Units.isOpenEmbedding_val.isEmbedding.isInducing.continuous_iff.mpr
  change Continuous (fun h : G => (lowerBlock h).val)
  apply continuous_matrix
  intro i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · simp only [lowerBlock_entries, Fin.cases_zero]
    exact continuous_const
  · simp only [lowerBlock_entries, Fin.cases_zero, Fin.cases_succ]
    exact continuous_const
  · simp only [lowerBlock_entries, Fin.cases_zero, Fin.cases_succ]
    exact continuous_const
  · simp only [lowerBlock_entries, Fin.cases_succ]
    have hVal : Continuous (Units.val : G → M) := Units.continuous_val
    exact (continuous_apply j).comp ((continuous_apply i).comp hVal)

private theorem lowerBlock_diagonalUnits (d : Fin m → ℝˣ) :
    lowerBlock (Iwasawa.diagonalUnits d) = Iwasawa.diagonalUnits (Fin.cons 1 d) := by
  apply Units.ext
  rw [lowerBlock_entries, Iwasawa.diagonalUnits_val, Iwasawa.diagonalUnits_val]
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · simp
  · simp [(Fin.succ_ne_zero j).symm]
  · simp
  · simp [Matrix.diagonal_apply]

/-- The Gram argument of the lower integration variable on the upper compact group. -/
def lowerGram (h : G) : M := h.val * h.val.transpose

/-- The angular argument of the lower cutoff, evaluated at the inverse variable. -/
def lowerAngle (h : G) : ℝ := offDiagonalSquare (signedOrthogonal (h⁻¹).val)

theorem continuous_lowerGram : Continuous (lowerGram : G → M) :=
  Units.continuous_val.matrix_mul Units.continuous_val.matrix_transpose

theorem continuous_lowerAngle : Continuous (lowerAngle : G → ℝ) := by
  have hSigned : Continuous (fun h : G => signedOrthogonal (h⁻¹).val) :=
    contDiffOn_signedOrthogonal.continuousOn.comp_continuous Units.continuous_coe_inv
      (fun h => Units.isUnit h⁻¹)
  exact contDiff_offDiagonalSquare.continuous.comp hSigned

theorem isCompact_lowerGram_preimage {S : Set M} (hS : IsCompact S)
    (hUnit : ∀ y ∈ S, IsUnit y) : IsCompact (lowerGram ⁻¹' S : Set G) := by
  have h := isCompact_support_preimage (isCompact_singleton (x := (1 : H)))
    (isCompact_rowGram_preimage hS) (fun x hx => hasFullRowRank_of_isUnit_rowGram (hUnit _ hx))
  convert h using 1
  ext x
  have hGram := rowGram_rowPoint_of_orthogonal x.val ((unitaryCompact ℝ (m + 1)).one_mem)
  simp only [mem_preimage, mem_ofPred_eq, mem_singleton_iff, exists_eq_left,
    lowerGram, hGram]

/-- The compact kernel with the two real scalar cutoffs removed. -/
def compactKernel (ds : List RealBlock) (F : H → ℂ) (h : G) (k : H) : ℂ :=
  F (lowerBlock h * k) * lowerCutoff ds (fun _ => 1) h⁻¹ * (Real.sqrt (|h.val.det|) : ℂ)

theorem continuous_compactKernel (ds : List RealBlock) {F : H → ℂ} (c : RealCharacterData)
    (hF : F ∈ principalSeries ℝ (m + 1) (realPositionCharacter (.character c :: ds))) :
    Continuous (fun p : G × H => compactKernel ds F p.1 p.2) := by
  have h1 := hF.1.continuous.comp ((continuous_lowerBlock.comp continuous_fst).mul continuous_snd)
  have h2 := (realGodementLowerCutoff m ds (fun _ => 1) contDiff_const).1.1.continuous.comp
    continuous_inv
  have hD : Continuous (fun h : G => |h.val.det|) := Units.continuous_val.matrix_det.abs
  exact (h1.mul (h2.comp continuous_fst)).mul
    (Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp (hD.comp continuous_fst)))

theorem lowerCutoff_factor (ds : List RealBlock) (b : ℝ → ℝ) (h : G) :
    lowerCutoff ds b h⁻¹ = (b (lowerAngle h) : ℂ) * lowerCutoff ds (fun _ => 1) h⁻¹ := by
  simp only [lowerCutoff, extension, lowerCompactTest, Complex.ofReal_one, one_mul]
  change _ * ((b (lowerAngle h) : ℂ) * _) = _
  rw [mul_left_comm]

private theorem lowerCutoff_one (ds : List RealBlock) :
    lowerCutoff ds (fun _ => 1) (1 : G) = 1 := by
  have h := (realGodementLowerCutoff m ds (fun _ => 1) contDiff_const).2
    (1 : Matrix.unitaryGroup (Fin m) ℝ)
  simpa [lowerCompactTest, Matrix.one_apply_eq] using h

private theorem principalSeriesCharacter_abs_eq_one (ds : List RealBlock)
    (d : Fin m → ℝˣ) (hd : ∀ i, |(d i : ℝ)| = 1) :
    principalSeriesCharacter ℝ m (realPositionCharacter ds) d =
      ∏ i : Fin m, realPositionCharacter ds i (d i) := by
  simp [principalSeriesCharacter, Real.norm_eq_abs, hd]

private theorem principalSeriesCharacter_cons_inv (c : RealCharacterData) (ds : List RealBlock)
    (d : Fin m → ℝˣ) (hd : ∀ i, |(d i : ℝ)| = 1) :
    principalSeriesCharacter ℝ (m + 1) (realPositionCharacter (.character c :: ds))
      (Fin.cons 1 d⁻¹) * principalSeriesCharacter ℝ m (realPositionCharacter ds) d = 1 := by
  have hInv (i : Fin m) : |((d⁻¹) i : ℝ)| = 1 := by
    simp [Pi.inv_apply, Units.val_inv_eq_inv_val, abs_inv, hd]
  let d' : Fin (m + 1) → ℝˣ := Fin.cons 1 d⁻¹
  have hCons (i : Fin (m + 1)) : |(d' i : ℝ)| = 1 :=
    Fin.cases (by simp [d']) (fun i => hInv i) i
  change principalSeriesCharacter ℝ (m + 1) (realPositionCharacter (.character c :: ds)) d' *
    principalSeriesCharacter ℝ m (realPositionCharacter ds) d = 1
  rw [principalSeriesCharacter_abs_eq_one _ _ hCons, principalSeriesCharacter_abs_eq_one _ _ hd,
    Fin.prod_univ_succ]
  dsimp only [d']
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_zero, Fin.val_succ, realPositionCharacter,
    map_one, Units.val_one, one_mul, ← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro i _
  simp only [Pi.inv_apply, realPositionCharacter_eq_charFun]
  rw [← charFun_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, charFun_one]

private theorem mem_unitaryCompact_of_lowerGram_eq_one {h : G} (hh : lowerGram h = 1) :
    h ∈ unitaryCompact ℝ m := by
  change h.val ∈ Matrix.unitaryGroup (Fin m) ℝ
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial]
  exact hh

/-- On the joint Gram and angular vanishing fiber, the two inducing signs cancel. -/
theorem compactKernel_eq_of_lowerGram_eq_one_of_lowerAngle_eq_zero
    (c : RealCharacterData) (ds : List RealBlock) {F : H → ℂ}
    (hF : F ∈ principalSeries ℝ (m + 1) (realPositionCharacter (.character c :: ds)))
    {h : G} (hGram : lowerGram h = 1) (hAngle : lowerAngle h = 0) (k : H) :
    compactKernel ds F h k = F k := by
  have hK := mem_unitaryCompact_of_lowerGram_eq_one hGram
  have hInvK : h⁻¹ ∈ unitaryCompact ℝ m := (unitaryCompact ℝ m).inv_mem hK
  let κ : Matrix.unitaryGroup (Fin m) ℝ := ⟨(h⁻¹).val, hInvK⟩
  have hSigned : signedOrthogonal (h⁻¹).val = (h⁻¹).val := by
    simpa [signReal] using signedOrthogonal_mul (b := (1 : M))
      Matrix.blockTriangular_one (fun _ => by simp)
      (mul_transpose_eq_one_of_mem hInvK)
  have hOff : offDiagonalSquare κ.val = 0 := by
    change offDiagonalSquare (signedOrthogonal (h⁻¹).val) = 0 at hAngle
    rwa [hSigned] at hAngle
  obtain ⟨a, ha⟩ := exists_signDiagonal_of_offDiagonalSquare_eq_zero κ hOff
  let d : Fin m → ℝˣ := fun i => signUnit (a i)
  have hd : h⁻¹ = Iwasawa.diagonalUnits d := by
    apply Units.ext
    rw [Iwasawa.diagonalUnits_val]
    calc
      _ = Matrix.diagonal (fun i => signReal (a i : ℝ)) := congrArg Subtype.val ha
      _ = _ := congrArg Matrix.diagonal (funext fun i => (signUnit_val (a i)).symm)
  have hh : h = Iwasawa.diagonalUnits d⁻¹ := by rw [map_inv, ← hd, inv_inv]
  have hB : lowerBlock h = Iwasawa.diagonalUnits (Fin.cons 1 d⁻¹) := by
    rw [hh, lowerBlock_diagonalUnits]
  have hCov : F (lowerBlock h * k) =
      principalSeriesCharacter ℝ (m + 1) (realPositionCharacter (.character c :: ds))
        (Fin.cons 1 d⁻¹) * F k := by
    rw [hB]
    simpa only [OneMemClass.coe_one, mul_one] using hF.2 (Fin.cons 1 d⁻¹) 1 k
  have hLower : lowerCutoff ds (fun _ => 1) h⁻¹ =
      principalSeriesCharacter ℝ m (realPositionCharacter ds) d := by
    rw [hd]
    have h := (realGodementLowerCutoff m ds (fun _ => 1) contDiff_const).1.2 d 1 1
    simpa only [OneMemClass.coe_one, mul_one, lowerCutoff_one] using h
  have hDet : |h.val.det| = 1 := MaximalParabolicIntegration.abs_det_unitary ⟨h, hK⟩
  rw [compactKernel, hDet, Real.sqrt_one, Complex.ofReal_one, mul_one, hCov, hLower,
    mul_right_comm, principalSeriesCharacter_cons_inv c ds d (fun i => abs_signUnit (a i)), one_mul]

/-- Within any compact invertible Gram window, the compact kernel is uniformly
close to the upper vector when the lower Gram and angular arguments are small. -/
def RealGodementCompactKernelStatement : Prop :=
  ∀ (m : ℕ) (c : RealCharacterData) (ds : List RealBlock)
    (F : Langlands.GeneralLinear (m + 1) ℝ → ℂ)
    (S : Set (Matrix (Fin m) (Fin m) ℝ)),
    F ∈ principalSeries ℝ (m + 1) (realPositionCharacter (.character c :: ds)) →
    IsCompact S → (∀ y ∈ S, IsUnit y) → ∀ ε > (0 : ℝ),
      ∃ δ > (0 : ℝ), ∀ h : Langlands.GeneralLinear m ℝ,
        lowerGram h ∈ S → dist (lowerGram h) 1 + lowerAngle h < δ →
        ∀ k ∈ unitaryCompact ℝ (m + 1), ‖compactKernel ds F h k - F k‖ < ε

theorem realGodementCompactKernel : RealGodementCompactKernelStatement := by
  intro m c ds F S hF hS hUnit ε hε
  let T : Set (Langlands.GeneralLinear m ℝ × Langlands.GeneralLinear (m + 1) ℝ) :=
    (lowerGram ⁻¹' S) ×ˢ (unitaryCompact ℝ (m + 1) : Set (Langlands.GeneralLinear (m + 1) ℝ))
  let D : Langlands.GeneralLinear m ℝ × Langlands.GeneralLinear (m + 1) ℝ → ℝ :=
    fun p => ‖compactKernel ds F p.1 p.2 - F p.2‖
  let A : Langlands.GeneralLinear m ℝ × Langlands.GeneralLinear (m + 1) ℝ → ℝ :=
    fun p => dist (lowerGram p.1) 1 + lowerAngle p.1
  let B : Set (Langlands.GeneralLinear m ℝ × Langlands.GeneralLinear (m + 1) ℝ) := T ∩ {p | ε ≤ D p}
  have hT : IsCompact T := (isCompact_lowerGram_preimage hS hUnit).prod
    (isCompact_iff_compactSpace.mpr (RealPrincipalSeriesDuality.compactSpace_unitaryCompact _))
  have hD : Continuous D := ((continuous_compactKernel ds c hF).sub
    (hF.1.continuous.comp continuous_snd)).norm
  have hA : Continuous A := ((continuous_lowerGram.comp continuous_fst).dist continuous_const).add
    (continuous_lowerAngle.comp continuous_fst)
  have hB : IsCompact B := hT.inter_right (isClosed_le continuous_const hD)
  have hPos (p : Langlands.GeneralLinear m ℝ × Langlands.GeneralLinear (m + 1) ℝ) (hp : p ∈ B) : 0 < A p := by
    have hAngle : 0 ≤ lowerAngle p.1 := offDiagonalSquare_nonneg _
    by_contra! h
    change dist (lowerGram p.1) 1 + lowerAngle p.1 ≤ 0 at h
    have hDist : dist (lowerGram p.1) 1 = 0 := le_antisymm (by linarith) dist_nonneg
    have hZero : lowerAngle p.1 = 0 := le_antisymm (by linarith) hAngle
    have hKernel := compactKernel_eq_of_lowerGram_eq_one_of_lowerAngle_eq_zero
      c ds hF (dist_eq_zero.mp hDist) hZero p.2
    have hBad : ε ≤ D p := hp.2
    simp only [D, hKernel, sub_self, norm_zero] at hBad
    exact hε.not_ge hBad
  by_cases hNonempty : B.Nonempty
  · obtain ⟨p, hp, hMin⟩ := hB.exists_isMinOn hNonempty hA.continuousOn
    refine ⟨A p, hPos p hp, fun h hh hSmall k hk => ?_⟩
    by_contra! hBad
    have hMem : (h, k) ∈ B := ⟨⟨hh, hk⟩, hBad⟩
    have hBound : A p ≤ A (h, k) := (isMinOn_iff.mp hMin) (h, k) hMem
    change A (h, k) < A p at hSmall
    exact (not_le_of_gt hSmall) hBound
  · refine ⟨1, zero_lt_one, fun h hh _ k hk => ?_⟩
    by_contra! hBad
    exact hNonempty ⟨(h, k), ⟨hh, hk⟩, hBad⟩

end Langlands.Global.RankinSelbergGlobal.RealGodement
