import Langlands.Global.RankinSelberg.ComplexGodementCompactPairing
import Langlands.Global.RankinSelberg.ComplexGodementRowDescent

/-! # Compact Gram cutoffs for complex Godement sections -/

noncomputable section

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open MeasureTheory Set
open scoped Matrix.Norms.Operator ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodement

local instance gramCutoffGLMeasurable (j : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear j ℂ) := borel _

variable {m : ℕ}

local notation "M" => Matrix (Fin m) (Fin m) ℂ
local notation "X" => Matrix (Fin m) (Fin (m + 1)) ℂ
local notation "Y" => Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ
local notation "G" => Langlands.GeneralLinear m ℂ
local notation "H" => Langlands.GeneralLinear (m + 1) ℂ

/-- The Gram matrix of the rows. -/
def rowGram (x : X) : M := x * x.conjTranspose

theorem contDiff_rowGram : ContDiff ℝ ∞ (rowGram : X → M) := by
  let fromEntries : (Fin m → Fin m → ℂ) →ₗ[ℝ] M :=
    { toFun := Matrix.of, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hEntry (i : Fin m) (j : Fin (m + 1)) : ContDiff ℝ ∞ (fun x : X => x i j) :=
    (LinearMap.toContinuousLinearMap
      ({ toFun := fun x => x i j, map_add' := fun _ _ => rfl,
         map_smul' := fun _ _ => rfl } : X →ₗ[ℝ] ℂ)).contDiff
  apply fromEntries.toContinuousLinearMap.contDiff.comp
  apply contDiff_pi.2
  intro i
  apply contDiff_pi.2
  intro j
  change ContDiff ℝ ∞ (fun x : X => ∑ l : Fin (m + 1), x i l * star (x j l))
  exact ContDiff.sum fun l _ => (hEntry i l).mul (Complex.conjCLE.contDiff.comp (hEntry j l))

private theorem re_rowGram_diag (x : X) (a : Fin m) :
    (rowGram x a a).re = ∑ b : Fin (m + 1), ‖x a b‖ ^ 2 := by
  simp only [rowGram, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [mul_comm]
  change ((starRingEnd ℂ) (x a b) * x a b).re = _
  rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

theorem isCompact_rowGram_preimage {S : Set M} (hS : IsCompact S) :
    IsCompact (rowGram ⁻¹' S : Set X) := by
  let traceReal (y : M) := y.trace.re
  have hTrace : Continuous traceReal :=
    Complex.reCLM.continuous.comp (Matrix.traceLinearMap (Fin m) ℝ ℂ).toContinuousLinearMap.continuous
  obtain ⟨B, hB⟩ := hS.bddAbove_image hTrace.continuousOn
  let R := |B| + 1
  apply (isCompact_closedBall (0 : ℂ) R).matrix.of_isClosed_subset
    (hS.isClosed.preimage contDiff_rowGram.continuous)
  intro x hx i j
  have hb : (rowGram x).trace.re ≤ B := hB (mem_image_of_mem _ hx)
  have hdiag : (rowGram x i i).re ≤ (rowGram x).trace.re := by
    rw [Matrix.trace, Complex.re_sum]
    change (rowGram x i i).re ≤ ∑ a : Fin m, (rowGram x a a).re
    exact Finset.single_le_sum (f := fun a => (rowGram x a a).re) (fun a _ => by
      rw [re_rowGram_diag]
      exact Finset.sum_nonneg (fun b _ => sq_nonneg ‖x a b‖)) (Finset.mem_univ i)
  have hSq : ‖x i j‖ ^ 2 ≤ B := by
    apply le_trans _ (hdiag.trans hb)
    rw [re_rowGram_diag]
    exact Finset.single_le_sum (fun b _ => sq_nonneg ‖x i b‖) (Finset.mem_univ j)
  rw [Metric.mem_closedBall, dist_zero_right]
  have hR : 0 ≤ R := by dsimp [R]; positivity
  apply (sq_le_sq₀ (norm_nonneg _) hR).mp
  calc
    ‖x i j‖ ^ 2 ≤ B := hSq
    _ ≤ |B| := le_abs_self B
    _ ≤ R ^ 2 := by dsimp [R]; nlinarith [abs_nonneg B, sq_nonneg |B|]

theorem hasFullRowRank_of_isUnit_rowGram {x : X} (h : IsUnit (rowGram x)) :
    HasFullRowRank x := by
  refine ⟨x.conjTranspose * (rowGram x)⁻¹, ?_⟩
  rw [← Matrix.mul_assoc]
  exact Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp h)

def lowerBlockMatrix (h : M) : Y :=
  trailingBlock h

/-- The block embedding `h ↦ diag(1,h)` with the first row indexed by zero. -/
def lowerBlock (h : G) : H :=
  trailingBlockGL h

theorem lowerBlock_val (h : G) : (lowerBlock h).val = lowerBlockMatrix h.val :=
  trailingBlockGL_val h

theorem det_lowerBlock (h : G) :
    determinant (lowerBlock h) = determinant h :=
  determinant_trailingBlockGL h

theorem trailingRows_lowerBlock_mul (h : G) (g : H) :
    trailingRows (lowerBlock h * g).val = h.val * trailingRows g.val := by
  ext i j
  change ((lowerBlock h).val * g.val) i.succ j = (h.val * trailingRows g.val) i j
  simp [lowerBlock_val, lowerBlockMatrix, Matrix.mul_apply, Fin.sum_univ_succ, trailingRows]

private theorem rowGram_trailingRows_of_unitary {k : H} (hk : k ∈ unitaryCompact ℂ (m + 1)) :
    rowGram (trailingRows k.val) = 1 := by
  ext i j
  have h := congrArg (fun A : Y => A i.succ j.succ) (Matrix.mem_unitaryGroup_iff.mp hk)
  simpa [rowGram, Matrix.star_eq_conjTranspose, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.one_apply, trailingRows] using h

theorem rowGram_mul_trailingRows_of_unitary (h : M) {k : H}
    (hk : k ∈ unitaryCompact ℂ (m + 1)) :
    rowGram (h * trailingRows k.val) = h * h.conjTranspose := by
  have hRows := rowGram_trailingRows_of_unitary hk
  simp only [rowGram, Matrix.conjTranspose_mul, Matrix.mul_assoc] at hRows ⊢
  rw [← Matrix.mul_assoc (trailingRows k.val) (trailingRows k.val).conjTranspose, hRows, one_mul]

/-- Cut off the normalized upper vector by a smooth function of the row Gram matrix. -/
def gramTest (c : ComplexCharacterData) (F : H → ℂ) (β : M → ℝ) (x : X) : ℂ :=
  (β (rowGram x) : ℂ) * normalizedOnRows c F x

theorem gramTest_eq_zero (c : ComplexCharacterData) (F : H → ℂ) {β : M → ℝ} {S : Set M}
    (hβZero : ∀ y ∉ S, β y = 0) {x : X} (hx : x ∉ rowGram ⁻¹' S) :
    gramTest c F β x = 0 := by
  simp [gramTest, hβZero (rowGram x) hx]

theorem contDiff_gramTest (c : ComplexCharacterData) (ds : List ComplexCharacterData) {F : H → ℂ}
    (hF : F ∈ complexStandardModule (m + 1) (c :: ds))
    {β : M → ℝ} {S : Set M} (hS : IsClosed S) (hSUnit : ∀ y ∈ S, IsUnit y)
    (hβ : ContDiff ℝ ∞ β) (hβZero : ∀ y ∉ S, β y = 0) :
    ContDiff ℝ ∞ (gramTest c F β) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : HasFullRowRank x
  · exact (Complex.ofRealCLM.contDiff.comp (hβ.comp contDiff_rowGram)).contDiffAt.mul
      ((contDiffOn_normalizedOnRows c ds hF).contDiffAt (isOpen_fullRowRank.mem_nhds hx))
  · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [(hS.preimage contDiff_rowGram.continuous).isOpen_compl.mem_nhds
      (show x ∉ rowGram ⁻¹' S from fun hxS => hx (hasFullRowRank_of_isUnit_rowGram
        (hSUnit _ hxS)))] with y hy
    exact gramTest_eq_zero c F hβZero hy

private theorem characterWeight_lowerBlock_shift (c : ComplexCharacterData) (h : G) :
    characterWeight c (((m : ℂ) + 1) / 2) (determinant h) =
      characterWeight c ((m : ℂ) / 2) (determinant (lowerBlock h)) * normPower (1 / 2) (determinant h) := by
  rw [det_lowerBlock]
  let z := determinant h
  change (c.character z : ℂ) * ComplexMaximalParabolicIntegration.normSqC (z : ℂ) ^
      (((m : ℂ) + 1) / 2) =
    ((c.character z : ℂ) * ComplexMaximalParabolicIntegration.normSqC (z : ℂ) ^ ((m : ℂ) / 2)) *
      ComplexMaximalParabolicIntegration.normSqC (z : ℂ) ^ (1 / 2 : ℂ)
  rw [mul_assoc, ← Complex.cpow_add _ _ (ComplexMaximalParabolicIntegration.normSqC_ne_zero z.ne_zero)]
  congr 2
  ring

theorem godementSection_gramTest (μ : Measure G) (c : ComplexCharacterData)
    (ds : List ComplexCharacterData) {F : H → ℂ} (hF : F ∈ complexStandardModule (m + 1) (c :: ds))
    (f : G → ℂ) (β : M → ℝ) (g : H) :
    godementSection μ c (gramTest c F β) f g =
      ∫ h : G, F (lowerBlock h * g) * f h⁻¹ * (β (rowGram (h.val * trailingRows g.val)) : ℂ) *
        normPower (1 / 2) (determinant h) ∂μ := by
  let w : H →* ℂ := (characterWeight c ((m : ℂ) / 2)).comp (determinant : H →* ℂˣ)
  have hDescent (q : H) : normalizedOnRows c F (trailingRows q.val) = F q / w q :=
    normalizedOnRows_trailingRows c ds hF q
  have hw (v : H) : w v ≠ 0 := ((Group.isUnit v).map w).ne_zero
  unfold godementSection godementSectionIntegrand
  rw [← integral_const_mul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro h
  have hRow := hDescent (lowerBlock (m := m) h * g)
  rw [trailingRows_lowerBlock_mul, map_mul] at hRow
  change w g * (((β (rowGram (h.val * trailingRows g.val)) : ℂ) *
    normalizedOnRows c F (h.val * trailingRows g.val)) * f h⁻¹ * _) = _
  rw [hRow, characterWeight_lowerBlock_shift]
  change w g * (((β (rowGram (h.val * trailingRows g.val)) : ℂ) *
    (F (lowerBlock h * g) / (w (lowerBlock h) * w g))) * f h⁻¹ *
    (w (lowerBlock h) * normPower (1 / 2) (determinant h))) = _
  field_simp [hw g, hw (lowerBlock h)]

/-- A compact Gram cutoff produces a smooth full-row-rank test and its
section is an integral of lower-block translates. -/
def ComplexGodementGramCutoffStatement : Prop :=
  ∀ (m : ℕ) (μ : Measure (Langlands.GeneralLinear m ℂ))
    (c : ComplexCharacterData) (ds : List ComplexCharacterData)
    (F : Langlands.GeneralLinear (m + 1) ℂ → ℂ) (f : Langlands.GeneralLinear m ℂ → ℂ)
    (β : Matrix (Fin m) (Fin m) ℂ → ℝ) (S : Set (Matrix (Fin m) (Fin m) ℂ)),
    F ∈ complexStandardModule (m + 1) (c :: ds) →
    IsCompact S → (∀ y ∈ S, IsUnit y) → ContDiff ℝ ∞ β → (∀ y ∉ S, β y = 0) →
      HasCompactSupport (gramTest c F β) ∧
      (∀ x ∈ tsupport (gramTest c F β), HasFullRowRank x) ∧ ContDiff ℝ ∞ (gramTest c F β) ∧
      ∀ k ∈ unitaryCompact ℂ (m + 1), godementSection μ c (gramTest c F β) f k =
        ∫ h : Langlands.GeneralLinear m ℂ, F (lowerBlock h * k) * f h⁻¹ *
          (β (h.val * h.val.conjTranspose) : ℂ) * normPower (1 / 2) (determinant h) ∂μ

theorem complexGodementGramCutoff : ComplexGodementGramCutoffStatement := by
  intro m μ c ds F f β S hF hS hUnit hβ hZero
  have hsupp : Function.support (gramTest c F β) ⊆ rowGram ⁻¹' S := by
    intro x hx
    by_contra hNot
    exact hx (gramTest_eq_zero c F hZero hNot)
  have hC := isCompact_rowGram_preimage hS
  refine ⟨HasCompactSupport.of_support_subset_isCompact hC hsupp, fun x hx => ?_,
    contDiff_gramTest c ds hF hS.isClosed hUnit hβ hZero, ?_⟩
  · exact hasFullRowRank_of_isUnit_rowGram (hUnit _ (closure_minimal hsupp hC.isClosed hx))
  · intro k hk
    rw [godementSection_gramTest μ c ds hF]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun h => by
      dsimp only
      rw [rowGram_mul_trailingRows_of_unitary h.val hk]

end Langlands.Global.RankinSelbergGlobal.ComplexGodement
