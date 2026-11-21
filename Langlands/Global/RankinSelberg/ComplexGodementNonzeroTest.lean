import Langlands.Global.RankinSelberg.ComplexGodementColumnProduct
import Langlands.Global.RankinSelberg.ComplexGodementContinuedSmooth
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! # A compact full-rank test with nonzero continued Godement value -/

noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Metric Set
open scoped Classical ContDiff Matrix.Norms.Operator SchwartzMap Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodement

open Langlands.GeneralLinear (determinant determinantContinuous)
open Langlands.HarmonicAnalysis (AdditiveHaarMeasure UnitaryAdditiveCharacter rowMeasure rowPairing
  rectangularJoin rectangularFirstColumns rectangularLastColumn continuous_rectangularJoin
  continuous_rectangularLastColumn partialFourierPlusIntegral rectangularJoin_castSucc
  rectangularJoin_last)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData complexScaledCharacter)
open Langlands.Analysis.SchwartzMatrixNorm (OperatorSchwartz operatorToEntry operatorToEntry_apply)
open ComplexGodementColumnProduct (columnProduct columnProduct_apply leadingColumns lastColumn)
open ComplexGodementWhittaker (augmentedPoint continuous_augmentedPoint augmentedPoint_castSucc kernelBase)
open ComplexGodementWhittakerFamily (HasUniformSimpleRootBound)
open ComplexGodementPartialFourier (partialSchwartz partialSchwartz_apply)
open ComplexGodementTranslatedBounds (complexGodementTranslatedBounds)
open ComplexGodementColumnChange (iteratedKernel iteratedKernel_eq)
open ComplexGodementAddedCharacter (rightTest rightTest_apply continuedValue)
open ArchimedeanLocal (complexNormalizedAbs)

attribute [local instance] ArchimedeanLocal.archimedeanComplexGLMeasurable
  ArchimedeanLocal.archimedeanComplexGLBorel

variable {r : ℕ}
local notation "G" => Langlands.GeneralLinear (r + 1) ℂ
local notation "G'" => Langlands.GeneralLinear (r + 1 + 1) ℂ
local notation "Square" => Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ
local notation "Rect" => Matrix (Fin (r + 1)) (Fin (r + 1 + 1)) ℂ
local notation "Col" => Fin (r + 1) → ℂ
local notation "Test" => OperatorSchwartz (r + 1) (r + 1 + 1)

private theorem integral_ne_zero_of_re_nonneg {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    (μ : Measure E) [μ.IsOpenPosMeasure] {f : E → ℂ} (hfc : Continuous f) (hfi : Integrable f μ)
    (h₀ : ∀ x, 0 ≤ (f x).re) {x : E} (hx : 0 < (f x).re) : (∫ y, f y ∂μ) ≠ 0 := by
  have hm : 0 < μ (Function.support (fun y => (f y).re)) := by
    have hs : IsOpen (Function.support (fun y => (f y).re)) :=
      isOpen_ne_fun (Complex.continuous_re.comp hfc) continuous_const
    apply measure_pos_of_nonempty_interior μ
    rw [hs.interior_eq]
    exact ⟨x, hx.ne'⟩
  have hi : Integrable (fun y => (f y).re) μ := Complex.reCLM.integrable_comp hfi
  have hp := (integral_pos_iff_support_of_nonneg h₀ hi).2 hm
  change 0 < ∫ y, Complex.reCLM (f y) ∂μ at hp
  rw [Complex.reCLM.integral_comp_comm hfi] at hp
  exact fun hz => by rw [hz, map_zero] at hp; exact (lt_irrefl 0) hp

private theorem exists_bump_in_neighborhood {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [HasContDiffBump E] {x : E} {S : Set E} (hS : S ∈ 𝓝 x) :
    ∃ b : ContDiffBump x, tsupport b ⊆ S := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hS
  let b : ContDiffBump x := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  exact ⟨b, by rw [b.tsupport_eq]; exact (closedBall_subset_ball (by dsimp [b]; linarith)).trans hball⟩

private theorem bump_at_center {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [HasContDiffBump E] {x : E} (b : ContDiffBump x) : b x = 1 :=
  b.one_of_mem_closedBall (mem_closedBall_self b.rIn_pos.le)

private def columnTransform (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ) (ψ : Col → ℂ) (z : Col) : ℂ :=
  ∫ y, ψ y * (complexScaledCharacter a).complex (rowPairing z y) ∂rowMeasure μ (r + 1)

private theorem continuous_pairing_right (z : Col) : Continuous (fun y : Col => rowPairing z y) := by
  unfold rowPairing
  exact continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_apply i)

private theorem continuous_pairing_left (y : Col) : Continuous (fun z : Col => rowPairing z y) := by
  unfold rowPairing
  exact continuous_finsetSum _ fun i _ => (continuous_apply i).mul continuous_const

private theorem continuous_columnTransform (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ) {ψ : Col → ℂ}
    (hψc : Continuous ψ) (hψi : Integrable ψ (rowMeasure μ (r + 1))) :
    Continuous (columnTransform μ a ψ) := by
  rw [continuous_iff_continuousAt]
  intro z
  unfold columnTransform
  apply continuousAt_of_dominated (bound := fun y => ‖ψ y‖)
  · exact Eventually.of_forall fun q => (hψc.mul ((complexScaledCharacter a).continuous_complex.comp
      (continuous_pairing_right q))).aestronglyMeasurable
  · exact Eventually.of_forall fun q => ae_of_all _ fun y => by
      rw [norm_mul, UnitaryAdditiveCharacter.norm_complex, mul_one]
  · exact hψi.norm
  · exact ae_of_all _ fun y => (continuous_const.mul ((complexScaledCharacter a).continuous_complex.comp
      (continuous_pairing_left y))).continuousAt

private theorem exists_compact_column_nonzero (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ) (z : Col) :
    ∃ ψ : 𝓢(Col, ℂ), HasCompactSupport ψ ∧ columnTransform μ a ψ z ≠ 0 := by
  let : μ.measure.IsAddHaarMeasure := μ.isAddHaar
  let c (y : Col) := (complexScaledCharacter a).complex (rowPairing z y)
  have hc : Continuous c := (complexScaledCharacter a).continuous_complex.comp (continuous_pairing_right z)
  have hc₀ : c 0 = 1 := by simp [c, rowPairing]
  have hS : {y : Col | 0 < (c y).re} ∈ 𝓝 (0 : Col) :=
    (isOpen_lt continuous_const (Complex.continuous_re.comp hc)).mem_nhds (by simp [hc₀])
  obtain ⟨b, hb⟩ := exists_bump_in_neighborhood hS
  let Ψ (y : Col) := (b y : ℂ)
  have hΨc : HasCompactSupport Ψ := by
    have he : Function.support Ψ = Function.support b := by ext y; simp [Ψ, Function.mem_support]
    unfold HasCompactSupport tsupport
    rw [he]
    exact b.hasCompactSupport
  let ψ : 𝓢(Col, ℂ) := hΨc.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff)
  have hi : Integrable (fun y => Ψ y * c y) (rowMeasure μ (r + 1)) := by
    refine ((Complex.continuous_ofReal.comp b.continuous).mul hc).integrable_of_hasCompactSupport ?_
    exact hΨc.mul_right
  refine ⟨ψ, hΨc, integral_ne_zero_of_re_nonneg _ ((Complex.continuous_ofReal.comp b.continuous).mul hc)
    hi (fun y => ?_) (x := 0) ?_⟩
  · change 0 ≤ ((b y : ℂ) * c y).re
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    by_cases hby : b y = 0
    · simp [hby]
    · exact mul_nonneg b.nonneg (hb (subset_tsupport _ hby) : 0 < (c y).re).le
  · change 0 < ((b (0 : Col) : ℂ) * c 0).re
    simp [bump_at_center, hc₀]

private theorem fullRowRank_join (g : G) (v : Col) : HasFullRowRank (rectangularJoin g.val v) := by
  let R : Matrix (Fin (r + 1 + 1)) (Fin (r + 1)) ℂ := fun i j => Fin.lastCases 0 (fun k => g⁻¹.val k j) i
  refine ⟨R, Matrix.ext fun i j => ?_⟩
  rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
  simp only [R, rectangularJoin_castSucc, rectangularJoin_last, Fin.lastCases_castSucc,
    Fin.lastCases_last, mul_zero, add_zero, ← Matrix.mul_apply, Units.mul_inv]

private theorem columnProduct_compact_full (Φ : 𝓢(Square, ℂ)) (ψ : 𝓢(Col, ℂ))
    (hΦ : HasCompactSupport Φ) (hψ : HasCompactSupport ψ) (hU : ∀ x ∈ tsupport Φ, IsUnit x) :
    HasCompactSupport (columnProduct Φ ψ) ∧ ∀ X ∈ tsupport (columnProduct Φ ψ), HasFullRowRank X := by
  let E := (fun p : Square × Col => rectangularJoin p.1 p.2) '' ((tsupport Φ) ×ˢ (tsupport ψ))
  have hE : IsCompact E := (hΦ.prod hψ).image continuous_rectangularJoin
  have hS : tsupport (columnProduct Φ ψ) ⊆ E := by
    apply closure_minimal _ hE.isClosed
    intro X hX
    change columnProduct Φ ψ X ≠ 0 at hX
    rw [columnProduct_apply] at hX
    refine ⟨(leadingColumns X, lastColumn X), ⟨subset_tsupport _ (left_ne_zero_of_mul hX),
      subset_tsupport _ (right_ne_zero_of_mul hX)⟩, ?_⟩
    ext i j
    induction j using Fin.lastCases <;> simp [rectangularJoin, leadingColumns, lastColumn]
  refine ⟨hE.of_isClosed_subset (isClosed_tsupport _) hS, ?_⟩
  intro X hX
  obtain ⟨⟨y, v⟩, ⟨hy, _⟩, rfl⟩ := hS hX
  obtain ⟨g, rfl⟩ := hU y hy
  exact fullRowRank_join g v

private theorem continuous_detPower (s : ℂ) :
    Continuous (fun g : G => ArchimedeanLocal.detPower complexNormalizedAbs g s) := by
  have hdet : Continuous (fun g : G => g.val.det) := Units.continuous_val.matrix_det
  have hlog : Continuous (fun g : G => Real.log (complexNormalizedAbs g.val.det)) :=
    (hdet.norm.pow 2).log fun g => pow_ne_zero 2 (norm_ne_zero_iff.mpr g.det_ne_zero)
  exact (continuous_const.mul (Complex.continuous_ofReal.comp hlog)).cexp

set_option maxHeartbeats 1700000 in
/-- At any parameters a nonzero smaller value at the identity is detected by some compact
full-rank test in the continued Godement integral at the identity. -/
theorem exists_compact_test_continuedValue_ne_zero {P : Type} (ν : Measure G) [ν.IsHaarMeasure]
    (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ) (d : ComplexCharacterData) (S : Set P) (W : P → G → ℂ)
    (hWc : ∀ p ∈ S, Continuous (W p)) (hWb : HasUniformSimpleRootBound S W)
    (p : P) (hp : p ∈ S) (hW : W p 1 ≠ 0) (s : ℂ) :
    ∃ Φ : Test, HasCompactSupport Φ ∧ (∀ X ∈ tsupport Φ, HasFullRowRank X) ∧
      continuedValue ν μ d a (operatorToEntry Φ) (W p) 1 s ≠ 0 := by
  let t : ℂ := (((r + 1 : ℕ) + 1 : ℂ) / 2) + s
  let z (h : G) := rectangularLastColumn (augmentedPoint h)
  obtain ⟨ψ, hψ, hψ₁⟩ := exists_compact_column_nonzero μ a (z 1)
  let J := columnTransform μ a ψ
  let F (h : G) := J (z h) * W p h⁻¹ * (d.character (determinant h) : ℂ) *
    ArchimedeanLocal.detPower complexNormalizedAbs h (t - 1)
  have hFc : Continuous F := by
    have hJ := continuous_columnTransform μ a ψ.continuous (ψ.continuous.integrable_of_hasCompactSupport hψ)
    exact (((hJ.comp (continuous_rectangularLastColumn.comp continuous_augmentedPoint)).mul
      ((hWc p hp).comp continuous_inv)).mul
        (Units.continuous_val.comp (d.character.continuous.comp determinantContinuous.continuous))).mul
          (continuous_detPower (t - 1))
  have hd1 (q : ℂ) : ArchimedeanLocal.detPower complexNormalizedAbs (1 : G) q = 1 := by
    simp [ArchimedeanLocal.detPower, complexNormalizedAbs]
  have hF₁ : F 1 ≠ 0 := by
    simpa only [F, inv_one, map_one, Units.val_one, mul_one, hd1] using mul_ne_zero hψ₁ hW
  let c := star (F 1)
  let V : Set G := {h | 0 < (c * F h).re}
  have hV : IsOpen V := isOpen_lt continuous_const (Complex.continuous_re.comp (continuous_const.mul hFc))
  have h1 : (1 : G) ∈ V := by
    change 0 < (star (F 1) * F 1).re
    rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.ofReal_re]
    exact Complex.normSq_pos.mpr hF₁
  let U : Set Square := Units.val '' V
  have hU : IsOpen U := Units.isOpenEmbedding_val.isOpenMap _ hV
  have hu : (1 : Square) ∈ U := ⟨1, h1, rfl⟩
  obtain ⟨b, hb⟩ := exists_bump_in_neighborhood (hU.mem_nhds hu)
  let B (X : Square) := c * (b X : ℂ)
  have hBc : ContDiff ℝ ∞ B := contDiff_const.mul (Complex.ofRealCLM.contDiff.comp b.contDiff)
  have hbB : tsupport B ⊆ tsupport b := by
    apply closure_minimal _ (isClosed_tsupport b)
    intro X hX
    apply subset_tsupport
    exact Complex.ofReal_ne_zero.mp (right_ne_zero_of_mul hX)
  have hB : HasCompactSupport B := b.hasCompactSupport.of_isClosed_subset (isClosed_tsupport B) hbB
  let φ := hB.toSchwartzMap hBc
  let Φ := columnProduct φ ψ
  obtain ⟨hΦ, hfull⟩ := columnProduct_compact_full φ ψ hB hψ fun x hx => by
    obtain ⟨g, _, rfl⟩ := hb (hbB hx)
    exact g.isUnit
  let Φₑ := operatorToEntry Φ
  let K := iteratedKernel (complexScaledCharacter a) μ d (rightTest (1 : G') Φₑ) (W p) t
  obtain ⟨I, N, A, _, _, hdom⟩ := complexGodementTranslatedBounds ν μ a d S W hWc hWb
    |(t - 1).re| (abs_nonneg _)
  have hKi : Integrable K ν := (hdom p hp t le_rfl 1 Φₑ).1
  have he (h : G) : K h = φ h.val * F h := by
    dsimp only [K]
    rw [iteratedKernel_eq (complexScaledCharacter a) μ d (rightTest (1 : G') Φₑ)
      (partialSchwartz a μ (rightTest (1 : G') Φₑ))
      (partialSchwartz_apply a μ (rightTest (1 : G') Φₑ))]
    rw [kernelBase, partialSchwartz_apply]
    have hPhi : partialFourierPlusIntegral (complexScaledCharacter a) μ (rightTest (1 : G') Φₑ)
        (augmentedPoint h) = φ h.val * J (z h) := by
      change _ = φ h.val * columnTransform μ a ψ (z h)
      unfold partialFourierPlusIntegral columnTransform
      rw [← integral_const_mul]
      apply integral_congr_ae
      refine ae_of_all _ fun y => ?_
      have hx : leadingColumns (rectangularJoin (rectangularFirstColumns (augmentedPoint h)) y) = h.val :=
        Matrix.ext fun i j => by simp [leadingColumns, rectangularFirstColumns]
      change (rightTest (1 : G') Φₑ) (rectangularJoin (rectangularFirstColumns (augmentedPoint h)) y) *
        _ = φ h.val * (ψ y * _)
      rw [rightTest_apply, Units.val_one, Matrix.mul_one]
      change Φ (rectangularJoin (rectangularFirstColumns (augmentedPoint h)) y) * _ = _
      have hy : lastColumn (rectangularJoin (rectangularFirstColumns (augmentedPoint h)) y) = y :=
        funext fun i => rectangularJoin_last _ _ i
      rw [columnProduct_apply, hx, hy, mul_assoc]
    rw [hPhi]
    unfold F
    ring
  have hKc : Continuous K := (continuous_congr he).mpr ((φ.continuous.comp Units.continuous_val).mul hFc)
  have hKre (h : G) : (K h).re = b h.val * (c * F h).re := by
    rw [he]
    change (c * (b h.val : ℂ) * F h).re = _
    rw [mul_assoc, mul_left_comm c (b h.val : ℂ), Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
  have hK₀ (h : G) : 0 ≤ (K h).re := by
    rw [hKre]
    by_cases hh : b h.val = 0
    · simp [hh]
    · obtain ⟨k, hk, he⟩ := hb (subset_tsupport _ hh)
      have hk' : k = h := Units.ext he
      exact mul_nonneg b.nonneg ((show 0 < (c * F k).re from hk).le.trans_eq (by rw [hk']))
  have hK₁ : 0 < (K 1).re := by
    rw [hKre, Units.val_one, bump_at_center, one_mul]
    exact h1
  have hInt : (∫ h, K h ∂ν) ≠ 0 := integral_ne_zero_of_re_nonneg ν hKc hKi hK₀ hK₁
  refine ⟨Φ, hΦ, hfull, ?_⟩
  unfold continuedValue
  have hdG' : ArchimedeanLocal.detPower complexNormalizedAbs (1 : G') s = 1 := by
    simp [ArchimedeanLocal.detPower, complexNormalizedAbs]
  rw [map_one determinant, map_one, mul_one, hdG', mul_one]
  exact mul_ne_zero (Units.ne_zero _) hInt

variable (r) in
/-- Compact full-rank detection of a nonzero smaller-rank value by the continued Godement integral. -/
def ComplexGodementNonzeroTestStatement : Prop :=
  ∀ {P : Type} (ν : Measure G) [ν.IsHaarMeasure] (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ)
    (d : ComplexCharacterData) (S : Set P) (W : P → G → ℂ),
    (∀ p ∈ S, Continuous (W p)) → HasUniformSimpleRootBound S W →
    ∀ p ∈ S, W p 1 ≠ 0 → ∀ s : ℂ,
      ∃ Φ : Test, HasCompactSupport Φ ∧ (∀ X ∈ tsupport Φ, HasFullRowRank X) ∧
        continuedValue ν μ d a (operatorToEntry Φ) (W p) 1 s ≠ 0

theorem complexGodementNonzeroTest : ComplexGodementNonzeroTestStatement r := by
  intro P ν hν μ a d S W hWc hWb p hp hW s
  exact exists_compact_test_continuedValue_ne_zero ν μ a d S W hWc hWb p hp hW s

end Langlands.Global.RankinSelbergGlobal.ComplexGodement
