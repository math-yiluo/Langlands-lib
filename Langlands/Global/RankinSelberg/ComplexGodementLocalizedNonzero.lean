import Langlands.Global.RankinSelberg.ComplexGodementAddedCharacter
import Langlands.Global.RankinSelberg.ComplexGodementUnitaryCutoff

/-! # Nonvanishing of the continued Godement integral on localized tests -/

noncomputable section

open MeasureTheory Set
open scoped Classical ContDiff Matrix.Norms.Elementwise SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodementAddedCharacter

open Langlands.GeneralLinear (determinant)
open Langlands.HarmonicAnalysis (AdditiveHaarMeasure rectangularJoin rectangularSplit
  rowMeasure rowPairing partialFourierPlusIntegral_join)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData complexScaledCharacter)
open ComplexGodement (HasFullRowRank characterWeight)
open ComplexGodementColumnChange (iteratedKernel iteratedKernel_eq)
open ComplexGodementPartialFourier (partialSchwartz partialSchwartz_apply)
open ComplexGodementWhittaker (augmentedPoint kernelBase)
open ArchimedeanLocal (complexNormalizedAbs)

attribute [local instance] ArchimedeanLocal.archimedeanComplexGLMeasurable
  ArchimedeanLocal.archimedeanComplexGLBorel

variable {r : ℕ}
local notation "m" => r + 1
local notation "I" => Fin m
local notation "H" => Langlands.GeneralLinear m ℂ
local notation "G" => Langlands.GeneralLinear (m + 1) ℂ
local notation "Mat" => Matrix I I ℂ
local notation "Rect" => Matrix I (Fin (m + 1)) ℂ
local notation "Col" => I → ℂ

private def cell (q : H × Col) : Rect := rectangularJoin q.1.val q.2

private theorem cell_isOpenEmbedding : Topology.IsOpenEmbedding (cell (r := r)) :=
  (rectangularSplit (K := ℂ) (n := m)).symm.isOpenEmbedding.comp
    ((Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℂ) m).prodMap
      Topology.IsOpenEmbedding.id)

private theorem cell_hasFullRowRank (q : H × Col) : HasFullRowRank (cell q) := by
  let Y : Matrix (Fin (m + 1)) I ℂ := fun i j => Fin.lastCases 0 (fun k => q.1⁻¹.val k j) i
  refine ⟨Y, ?_⟩
  have h : (cell q) * Y = q.1.val * q.1⁻¹.val := by
    ext i j
    rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_castSucc]
    simp [cell, Y]
  rw [h, ← Units.val_mul, mul_inv_cancel, Units.val_one]

private def amplitude (a : ℂˣ) (d : ComplexCharacterData) (W : H → ℂ) (t : ℂ)
    (q : H × Col) : ℂ :=
  (complexScaledCharacter a).complex (rowPairing (Langlands.RankinSelberg.lastRow q.1⁻¹) q.2) *
    W q.1⁻¹ * (d.character (determinant q.1) : ℂ) * ArchimedeanLocal.detPower complexNormalizedAbs q.1 t

private theorem continuous_amplitude (a : ℂˣ) (d : ComplexCharacterData) {W : H → ℂ}
    (hW : Continuous W) (t : ℂ) : Continuous (amplitude a d W t) := by
  have h1 : Continuous (fun q : H × Col => rowPairing (Langlands.RankinSelberg.lastRow q.1⁻¹) q.2) := by
    unfold rowPairing
    apply continuous_finsetSum
    intro i _
    have hl : Continuous (fun q : H × Col => q.1⁻¹.val (Fin.last r) i) :=
      (Units.continuous_val.comp (continuous_inv.comp continuous_fst)).matrix_elem _ _
    exact hl.mul ((continuous_apply i).comp continuous_snd)
  have h2 : Continuous (fun q : H × Col => (d.character (determinant q.1) : ℂ)) :=
    Units.continuous_val.comp (d.character.continuous.comp
      (Langlands.GeneralLinear.determinantContinuous.continuous.comp continuous_fst))
  have h3 : Continuous (fun q : H × Col => ArchimedeanLocal.detPower complexNormalizedAbs q.1 t) := by
    have hlog : Continuous (fun q : H × Col => Real.log (complexNormalizedAbs q.1.val.det)) :=
      (((Units.continuous_val.comp continuous_fst).matrix_det).norm.pow 2).log
        (fun q => (pow_pos (norm_pos_iff.mpr (Matrix.GeneralLinearGroup.det_ne_zero q.1)) 2).ne')
    exact ((Complex.continuous_ofReal.comp hlog).const_mul t).cexp
  exact ((((complexScaledCharacter a).continuous_complex.comp h1).mul
    (hW.comp (continuous_inv.comp continuous_fst))).mul h2).mul h3

private theorem continuedValue_one_kernel (ν : Measure H) (μ : AdditiveHaarMeasure ℂ)
    (a : ℂˣ) (d : ComplexCharacterData) (Φ : 𝓢(Rect, ℂ)) (W : H → ℂ) (s : ℂ) :
    continuedValue ν μ d a Φ W 1 s = (d.character ((-1 : ℂˣ) ^ m) : ℂ) *
      ∫ h, iteratedKernel (complexScaledCharacter a) μ d Φ W ((((m : ℕ) + 1 : ℂ) / 2) + s) h ∂ν := by
  have hΦ : rightTest (1 : G) Φ = Φ := by
    ext X
    simp [rightTest_apply]
  rw [continuedValue, hΦ, map_one, map_one, mul_one]
  have he : ArchimedeanLocal.detPower complexNormalizedAbs (1 : G) s = 1 := by
    simp [ArchimedeanLocal.detPower, complexNormalizedAbs]
  rw [he, mul_one]

private theorem inner_eq_iteratedKernel (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ)
    (d : ComplexCharacterData) (Φ : 𝓢(Rect, ℂ)) (W : H → ℂ) (t : ℂ) (h : H) :
    (∫ y, Φ (cell (h, y)) * amplitude a d W (t - 1) (h, y) ∂rowMeasure μ m) =
      iteratedKernel (complexScaledCharacter a) μ d Φ W t h := by
  rw [iteratedKernel_eq _ _ _ _ (partialSchwartz a μ Φ) (partialSchwartz_apply a μ Φ), kernelBase,
    partialSchwartz_apply]
  have hp : augmentedPoint h = rectangularJoin h.val (Langlands.RankinSelberg.lastRow h⁻¹) := by
    ext i j
    refine Fin.lastCases ?_ (fun k => ?_) j <;> simp [Langlands.RankinSelberg.lastRow]
  rw [hp, partialFourierPlusIntegral_join]
  simp only [amplitude, ← mul_assoc, cell, integral_mul_const, rowPairing]

/-- At a nonzero smaller coefficient, the continued Godement functional has a nonzero value
on a compact rectangular test supported in the full-row-rank locus. -/
def ComplexGodementLocalizedNonzeroStatement : Prop :=
  ∀ (ν : Measure H) [ν.IsHaarMeasure] (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ)
    (d : ComplexCharacterData) (s : ℂ) (W : H → ℂ), Continuous W → (∃ g, W g ≠ 0) →
    ∃ Φ : 𝓢(Rect, ℂ), HasCompactSupport Φ ∧ (∀ X ∈ tsupport Φ, HasFullRowRank X) ∧
      continuedValue ν μ d a Φ W 1 s ≠ 0

set_option maxHeartbeats 850000 in
theorem complexGodementLocalizedNonzero : ComplexGodementLocalizedNonzeroStatement (r := r) := by
  intro ν hν μ a d s W hW hWnz
  let e := Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℂ) m
  let : LocallyCompactSpace H := e.locallyCompactSpace
  let : SecondCountableTopology H := e.secondCountableTopology
  let : μ.measure.IsAddHaarMeasure := μ.isAddHaar
  let t : ℂ := (((m : ℕ) + 1 : ℂ) / 2) + s
  let A := amplitude a d W (t - 1)
  obtain ⟨g, hg⟩ := hWnz
  let q₀ : H × Col := (g⁻¹, 0)
  have hA₀ : A q₀ ≠ 0 := by
    unfold A amplitude
    have hψ : (complexScaledCharacter a).complex (rowPairing (Langlands.RankinSelberg.lastRow g) 0) = 1 := by
      simp [rowPairing]
    simp only [q₀, inv_inv, hψ, one_mul]
    exact mul_ne_zero (mul_ne_zero hg (d.character (determinant g⁻¹)).ne_zero) (Complex.exp_ne_zero _)
  let c : ℂ := star (A q₀)
  let O : Set (H × Col) := {q | 0 < (c * A q).re}
  have hO : IsOpen O := isOpen_lt continuous_const
    (Complex.continuous_re.comp ((continuous_amplitude a d hW _).const_mul c))
  have hq₀ : q₀ ∈ O := by
    change 0 < (star (A q₀) * A q₀).re
    rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.ofReal_re]
    exact Complex.normSq_pos.2 hA₀
  let U := cell '' O
  have hU : IsOpen U := cell_isOpenEmbedding.isOpenMap O hO
  have hU₀ : {cell q₀} ⊆ U := singleton_subset_iff.2 ⟨q₀, hq₀, rfl⟩
  obtain ⟨K, hK, h₀, hKU⟩ := exists_compact_between (isCompact_singleton (x := cell q₀)) hU hU₀
  obtain ⟨b, hbD, hbRange, hbSupp, hbOne⟩ := exists_contDiff_support_eq_eq_one_iff
    (n := ⊤) isOpen_interior isClosed_singleton h₀
  let bC (X : Rect) : ℂ := b X
  have hbCsub : tsupport bC ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro X hX
    have hbX : X ∈ Function.support b := fun h => hX (by simp [bC, h])
    rw [hbSupp] at hbX
    exact interior_subset hbX
  have hbC : HasCompactSupport bC := hK.of_isClosed_subset (isClosed_tsupport _) hbCsub
  let Φ : 𝓢(Rect, ℂ) := hbC.toSchwartzMap (Complex.ofRealCLM.contDiff.comp hbD)
  have hΦc : HasCompactSupport Φ := hbC
  have hΦU : tsupport Φ ⊆ U := hbCsub.trans hKU
  have hΦr : ∀ X ∈ tsupport Φ, HasFullRowRank X := by
    intro X hX
    obtain ⟨q, _, rfl⟩ := hΦU hX
    exact cell_hasFullRowRank q
  let F (q : H × Col) : ℂ := Φ (cell q) * (c * A q)
  have hFc : Continuous F := (Φ.continuous.comp cell_isOpenEmbedding.continuous).mul
    ((continuous_amplitude a d hW _).const_mul c)
  have hKc : IsCompact (cell ⁻¹' tsupport Φ) := by
    apply cell_isOpenEmbedding.isEmbedding.isCompact_iff.2
    rw [Set.image_preimage_eq_of_subset]
    · exact hΦc
    · exact hΦU.trans (Set.image_subset_range _ _)
  have hFcs : HasCompactSupport F := by
    refine HasCompactSupport.of_support_subset_isCompact hKc fun q hq => ?_
    apply subset_tsupport Φ
    exact fun h => hq (by simp [F, h])
  have hRecs : HasCompactSupport (fun q => (F q).re) := by
    refine HasCompactSupport.of_support_subset_isCompact hKc fun q hq => ?_
    apply subset_tsupport Φ
    exact fun h => hq (by simp [F, h])
  have hRe : ∀ q, 0 ≤ (F q).re := by
    intro q
    by_cases hq : Φ (cell q) = 0
    · simp [F, hq]
    · have hh : q ∈ O := by
        obtain ⟨q', hq', he⟩ := hΦU (subset_tsupport Φ hq)
        exact (cell_isOpenEmbedding.injective he) ▸ hq'
      change 0 ≤ ((b (cell q) : ℂ) * (c * A q)).re
      rw [Complex.re_ofReal_mul]
      exact mul_nonneg (hbRange ⟨cell q, rfl⟩).1 hh.le
  have hRe₀ : (F q₀).re ≠ 0 := by
    change ((b (cell q₀) : ℂ) * (c * A q₀)).re ≠ 0
    have hb : b (cell q₀) = 1 := (hbOne _).1 (mem_singleton _)
    rw [hb, Complex.ofReal_one, one_mul]
    exact hq₀.ne'
  let η := rowMeasure μ m
  have hIF : Integrable F (ν.prod η) := hFc.integrable_of_hasCompactSupport hFcs
  have hpos : 0 < ∫ q, (F q).re ∂ν.prod η :=
    (Complex.continuous_re.comp hFc).integral_pos_of_hasCompactSupport_nonneg_nonzero hRecs hRe hRe₀
  have hI : (∫ q, F q ∂ν.prod η) ≠ 0 := by
    intro he
    have hr : (∫ q, (F q).re ∂ν.prod η) = (∫ q, F q ∂ν.prod η).re := integral_re hIF
    rw [hr, he, Complex.zero_re] at hpos
    exact (lt_irrefl 0) hpos
  refine ⟨Φ, hΦc, hΦr, ?_⟩
  have hfactor : (∫ q, F q ∂ν.prod η) = c *
      ∫ h, iteratedKernel (complexScaledCharacter a) μ d Φ W t h ∂ν := by
    rw [integral_prod F hIF, ← integral_const_mul]
    apply integral_congr_ae (ae_of_all _ fun h => ?_)
    have he (y : Col) : F (h, y) = c * (Φ (cell (h, y)) * A (h, y)) := by unfold F; ring
    simp_rw [he]
    rw [integral_const_mul, inner_eq_iteratedKernel]
  rw [continuedValue_one_kernel]
  exact mul_ne_zero (d.character ((-1 : ℂˣ) ^ m)).ne_zero (right_ne_zero_of_mul
    (show c * (∫ h, iteratedKernel (complexScaledCharacter a) μ d Φ W t h ∂ν) ≠ 0 from hfactor ▸ hI))

end Langlands.Global.RankinSelbergGlobal.ComplexGodementAddedCharacter
