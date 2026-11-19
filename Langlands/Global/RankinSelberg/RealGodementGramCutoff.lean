import Langlands.Global.RankinSelberg.RealGodementRowDescent

/-! # Compact Gram cutoffs for real Godement sections -/

noncomputable section

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open MeasureTheory Set
open scoped Matrix.Norms.Operator ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

variable {m : ℕ}

local notation "M" => Matrix (Fin m) (Fin m) ℝ
local notation "X" => Matrix (Fin m) (Fin (m + 1)) ℝ
local notation "Y" => Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ
local notation "G" => Langlands.GeneralLinear m ℝ
local notation "H" => Langlands.GeneralLinear (m + 1) ℝ

/-- The Gram matrix of the rows. -/
def rowGram (x : X) : M := x * x.transpose

theorem contDiff_rowGram : ContDiff ℝ ∞ (rowGram : X → M) := by
  let fromEntries : (Fin m → Fin m → ℝ) →ₗ[ℝ] M :=
    { toFun := Matrix.of, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hEntry (i : Fin m) (j : Fin (m + 1)) : ContDiff ℝ ∞ (fun x : X => x i j) :=
    (LinearMap.toContinuousLinearMap
      ({ toFun := fun x => x i j, map_add' := fun _ _ => rfl,
         map_smul' := fun _ _ => rfl } : X →ₗ[ℝ] ℝ)).contDiff
  apply fromEntries.toContinuousLinearMap.contDiff.comp
  apply contDiff_pi.2
  intro i
  apply contDiff_pi.2
  intro j
  change ContDiff ℝ ∞ (fun x : X => ∑ l : Fin (m + 1), x i l * x j l)
  exact ContDiff.sum fun l _ => (hEntry i l).mul (hEntry j l)

theorem isCompact_rowGram_preimage {S : Set M} (hS : IsCompact S) :
    IsCompact (rowGram ⁻¹' S : Set X) := by
  have hTrace : Continuous (Matrix.trace : M → ℝ) :=
    (Matrix.traceLinearMap (Fin m) ℝ ℝ).toContinuousLinearMap.continuous
  obtain ⟨B, hB⟩ := hS.bddAbove_image hTrace.continuousOn
  let R := |B| + 1
  apply ((isCompact_Icc : IsCompact (Icc (-R) R)).matrix).of_isClosed_subset
    (hS.isClosed.preimage contDiff_rowGram.continuous)
  intro x hx i j
  have hd (a : Fin m) : rowGram x a a = ∑ b : Fin (m + 1), x a b ^ 2 := by
    simp only [rowGram, Matrix.mul_apply, Matrix.transpose_apply, pow_two]
  have hb : (rowGram x).trace ≤ B := hB (mem_image_of_mem _ hx)
  have hdiag : rowGram x i i ≤ (rowGram x).trace :=
    Finset.single_le_sum (fun a _ => hd a ▸ Finset.sum_nonneg (fun b _ => sq_nonneg (x a b)))
      (Finset.mem_univ i)
  have hSq : x i j ^ 2 ≤ B := by
    apply le_trans _ (hdiag.trans hb)
    rw [hd]
    exact Finset.single_le_sum (fun b _ => sq_nonneg (x i b)) (Finset.mem_univ j)
  apply abs_le_of_sq_le_sq' _ (by positivity : 0 ≤ R)
  calc
    x i j ^ 2 ≤ B := hSq
    _ ≤ |B| := le_abs_self B
    _ ≤ R ^ 2 := by dsimp [R]; nlinarith [abs_nonneg B, sq_nonneg |B|]

theorem hasFullRowRank_of_isUnit_rowGram {x : X} (h : IsUnit (rowGram x)) :
    HasFullRowRank x := by
  refine ⟨x.transpose * (rowGram x)⁻¹, ?_⟩
  rw [← Matrix.mul_assoc]
  exact Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp h)

private def lowerBlockMatrix (h : M) : Y :=
  Fin.cases (Fin.cases 1 fun _ => 0) (fun i => Fin.cases 0 (h i))

private theorem det_lowerBlockMatrix (h : M) : (lowerBlockMatrix h).det = h.det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  have hMinor : (lowerBlockMatrix h).submatrix Fin.succ (0 : Fin (m + 1)).succAbove = h := by
    ext i j
    simp [lowerBlockMatrix]
  rw [hMinor]
  simp [lowerBlockMatrix]

/-- The block embedding `h ↦ diag(1,h)` with the first row indexed by zero. -/
def lowerBlock (h : G) : H :=
  ((Matrix.isUnit_iff_isUnit_det (lowerBlockMatrix h.val)).mpr
    (det_lowerBlockMatrix h.val ▸ (Matrix.GeneralLinearGroup.det h).isUnit)).unit

private theorem lowerBlock_val (h : G) : (lowerBlock h).val = lowerBlockMatrix h.val :=
  IsUnit.unit_spec _

theorem det_lowerBlock (h : G) :
    Matrix.GeneralLinearGroup.det (lowerBlock h) = Matrix.GeneralLinearGroup.det h := by
  apply Units.ext
  change (lowerBlock h).val.det = h.val.det
  rw [lowerBlock_val, det_lowerBlockMatrix]

theorem lastRows_lowerBlock_mul (h : G) (g : H) :
    lastRows (lowerBlock h * g).val = rowPoint h.val g := by
  ext i j
  change ((lowerBlock h).val * g.val) i.succ j = (h.val * lastRows g.val) i j
  simp [lowerBlock_val, lowerBlockMatrix, Matrix.mul_apply, Fin.sum_univ_succ, lastRows]

private theorem rowGram_lastRows_of_orthogonal {k : H} (hk : k ∈ unitaryCompact ℝ (m + 1)) :
    rowGram (lastRows k.val) = 1 := by
  ext i j
  have h := congrArg (fun A : Y => A i.succ j.succ) (GramFormula.mul_transpose_eq_one_of_mem hk)
  simpa [rowGram, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, lastRows] using h

theorem rowGram_rowPoint_of_orthogonal (h : M) {k : H} (hk : k ∈ unitaryCompact ℝ (m + 1)) :
    rowGram (rowPoint h k) = h * h.transpose := by
  have hRows := rowGram_lastRows_of_orthogonal hk
  simp only [rowGram, rowPoint, Matrix.transpose_mul, Matrix.mul_assoc] at hRows ⊢
  rw [← Matrix.mul_assoc (lastRows k.val) (lastRows k.val).transpose, hRows, one_mul]

/-- Cut off the normalized upper vector by a smooth function of the row Gram matrix. -/
def gramTest (c : RealCharacterData) (F : H → ℂ) (β : M → ℝ) (x : X) : ℂ :=
  (β (rowGram x) : ℂ) * normalizedOnRows c F x

theorem gramTest_eq_zero (c : RealCharacterData) (F : H → ℂ) {β : M → ℝ} {S : Set M}
    (hβZero : ∀ y ∉ S, β y = 0) {x : X} (hx : x ∉ rowGram ⁻¹' S) :
    gramTest c F β x = 0 := by
  simp [gramTest, hβZero (rowGram x) hx]

theorem contDiff_gramTest (c : RealCharacterData) (ds : List RealBlock) {F : H → ℂ}
    (hF : F ∈ principalSeries ℝ (m + 1) (realPositionCharacter (.character c :: ds)))
    {β : M → ℝ} {S : Set M} (hS : IsClosed S) (hSUnit : ∀ y ∈ S, IsUnit y)
    (hβ : ContDiff ℝ ∞ β) (hβZero : ∀ y ∉ S, β y = 0) :
    ContDiff ℝ ∞ (gramTest c F β) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : HasFullRowRank x
  · exact (Complex.ofRealCLM.contDiff.comp (hβ.comp contDiff_rowGram)).contDiffAt.mul
      ((realGodementRowDescent m c ds F hF).1.contDiffAt (isOpen_fullRowRank.mem_nhds hx))
  · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [(hS.preimage contDiff_rowGram.continuous).isOpen_compl.mem_nhds
      (show x ∉ rowGram ⁻¹' S from fun hxS => hx (hasFullRowRank_of_isUnit_rowGram
        (hSUnit _ hxS)))] with y hy
    exact gramTest_eq_zero c F hβZero hy

private theorem determinantWeight_lowerBlock_shift (c : RealCharacterData) (h : G) :
    determinantWeight c (((m : ℂ) + 1) / 2) h =
      determinantWeight c ((m : ℂ) / 2) (lowerBlock h) *
        ((|h.val.det| : ℝ) : ℂ) ^ (1 / 2 : ℂ) := by
  let t := Matrix.GeneralLinearGroup.det h
  have ht : ((|(t : ℝ)| : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr t.ne_zero)
  change (c.character t : ℂ) * ((|(t : ℝ)| : ℝ) : ℂ) ^ (((m : ℂ) + 1) / 2) =
    (c.character (Matrix.GeneralLinearGroup.det (lowerBlock h)) : ℂ) *
      ((|(Matrix.GeneralLinearGroup.det (lowerBlock h) : ℝ)| : ℝ) : ℂ) ^ ((m : ℂ) / 2) *
      ((|(t : ℝ)| : ℝ) : ℂ) ^ (1 / 2 : ℂ)
  rw [det_lowerBlock, mul_assoc, ← Complex.cpow_add _ _ ht]
  congr 2
  ring

theorem sectionValue_gramTest [MeasurableSpace (Langlands.GeneralLinear m ℝ)]
    (μ : Measure (Langlands.GeneralLinear m ℝ)) (c : RealCharacterData) (ds : List RealBlock) {F : H → ℂ}
    (hF : F ∈ principalSeries ℝ (m + 1) (realPositionCharacter (.character c :: ds)))
    (f : G → ℂ) (β : M → ℝ) (g : H) :
    sectionValue μ c f (gramTest c F β) g =
      ∫ h : Langlands.GeneralLinear m ℝ, F (lowerBlock h * g) * f h⁻¹ * (β (rowGram (rowPoint h.val g)) : ℂ) *
        ((|h.val.det| : ℝ) : ℂ) ^ (1 / 2 : ℂ) ∂μ := by
  let w : H →* ℂ := determinantWeight c ((m : ℂ) / 2)
  have hDescent (q : H) : normalizedOnRows c F (lastRows q.val) = F q / w q :=
    (realGodementRowDescent m c ds F hF).2 q
  unfold sectionValue innerIntegral
  rw [← integral_const_mul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro h
  have hRow := hDescent (lowerBlock (m := m) h * g)
  rw [lastRows_lowerBlock_mul, map_mul] at hRow
  have hw (g' : H) : w g' ≠ 0 := by
    have hn := map_mul w g' g'⁻¹
    rw [mul_inv_cancel, map_one] at hn
    exact left_ne_zero_of_mul (hn.symm.trans_ne one_ne_zero)
  change w g * ((f h⁻¹ * determinantWeight c (((m : ℂ) + 1) / 2) h) *
    ((β (rowGram (rowPoint h.val g)) : ℂ) * normalizedOnRows c F (rowPoint h.val g))) = _
  rw [hRow, determinantWeight_lowerBlock_shift]
  change w g * ((f h⁻¹ * (w (lowerBlock h) * ((|h.val.det| : ℝ) : ℂ) ^ (1 / 2 : ℂ))) *
    ((β (rowGram (rowPoint h.val g)) : ℂ) * (F (lowerBlock h * g) / (w (lowerBlock h) * w g)))) = _
  field_simp [hw g, hw (lowerBlock h)]

/-- A compact Gram cutoff produces a smooth test of compact full-row-rank support.
On the compact subgroup its section is an integral of lower block translates. -/
def RealGodementGramCutoffStatement : Prop :=
  ∀ (m : ℕ) [MeasurableSpace (Langlands.GeneralLinear m ℝ)]
    (μ : Measure (Langlands.GeneralLinear m ℝ)) (c : RealCharacterData) (ds : List RealBlock)
    (F : Langlands.GeneralLinear (m + 1) ℝ → ℂ)
    (f : Langlands.GeneralLinear m ℝ → ℂ)
    (β : Matrix (Fin m) (Fin m) ℝ → ℝ) (S : Set (Matrix (Fin m) (Fin m) ℝ)),
    F ∈ principalSeries ℝ (m + 1) (realPositionCharacter (.character c :: ds)) →
    IsCompact S → (∀ y ∈ S, IsUnit y) → ContDiff ℝ ∞ β → (∀ y ∉ S, β y = 0) →
      IsCompact (rowGram ⁻¹' S) ∧ (∀ x ∈ rowGram ⁻¹' S, HasFullRowRank x) ∧
      ContDiff ℝ ∞ (gramTest c F β) ∧ (∀ x ∉ rowGram ⁻¹' S, gramTest c F β x = 0) ∧
      ∀ k ∈ unitaryCompact ℝ (m + 1), sectionValue μ c f (gramTest c F β) k =
        ∫ h : Langlands.GeneralLinear m ℝ, F (lowerBlock h * k) * f h⁻¹ * (β (h.val * h.val.transpose) : ℂ) *
          ((|h.val.det| : ℝ) : ℂ) ^ (1 / 2 : ℂ) ∂μ

theorem realGodementGramCutoff : RealGodementGramCutoffStatement := by
  intro m _ μ c ds F f β S hF hS hUnit hβ hZero
  refine ⟨isCompact_rowGram_preimage hS, fun x hx => hasFullRowRank_of_isUnit_rowGram
    (hUnit (rowGram x) hx), contDiff_gramTest c ds hF hS.isClosed hUnit hβ hZero,
    fun _ hx => gramTest_eq_zero c F hZero hx, ?_⟩
  intro k hk
  calc
    _ = ∫ h : Langlands.GeneralLinear m ℝ, F (lowerBlock h * k) * f h⁻¹ * (β (rowGram (rowPoint h.val k)) : ℂ) *
        ((|h.val.det| : ℝ) : ℂ) ^ (1 / 2 : ℂ) ∂μ := sectionValue_gramTest μ c ds hF f β k
    _ = _ := by simp only [rowGram_rowPoint_of_orthogonal _ hk]

end Langlands.Global.RankinSelbergGlobal.RealGodement
