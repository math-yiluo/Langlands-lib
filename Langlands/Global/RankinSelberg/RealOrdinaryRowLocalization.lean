import Langlands.Global.RankinSelberg.RealLowerBlockChart
import Langlands.Global.RankinSelberg.RealEqualConvergence
import Langlands.Representation.RankinSelberg.InducedTailIntermediateLocalization
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! # Localization at the last row of a real unipotent quotient -/

noncomputable section

open Filter MeasureTheory MeasureTheory.Measure Set Topology
open scoped ENNReal NNReal FourierTransform RealInnerProductSpace Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealOrdinaryRowLocalization

open Langlands.GeneralLinear Langlands.QuotientIntegration
open Langlands.RankinSelberg (LeftUnipotentQuotient lastRow lastRow_unipotent_mul)
open ArchimedeanLocal RealLowerBlockChart

attribute [local instance] archimedeanRealGLMeasurable archimedeanRealGLBorel
  archimedeanRealNMeasurable archimedeanRealNBorel archimedeanRealQMeasurable
  archimedeanRealQBorel RealRankZero.unitsMeasurable RealRankZero.unitsBorel

local notation "G" => fun r => Langlands.GeneralLinear (r + 1) ℝ
local notation "N" => fun r => Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ
local notation "Q" => fun r => LeftUnipotentQuotient r ℝ
local notation "Z" => fun r => (Fin (r + 1) → ℝ) × ℝˣ
local notation "Row" => fun r => Fin (r + 1) → ℝ

variable {r : ℕ}

/-- The last row associated to the lower-block chart coordinates. -/
def row (z : Z r) : Row (r + 1) := Fin.snoc z.1 (z.2 : ℝ)

/-- The section of the last-row map with identity leading block. -/
def sectionGL (z : Z r) : G (r + 1) :=
  lowerBlockPair (1 : G r) (rowEquiv z.1) (unitsLower z.2)

theorem continuous_sectionGL : Continuous (sectionGL (r := r)) := by
  have hc : Continuous (rowEquiv (n := r) : Row r → Matrix (Fin 1) (Fin (r + 1)) ℝ) :=
    continuous_pi fun _ => continuous_id
  exact continuous_lowerBlockPair.comp (continuous_const.prodMk
    ((hc.comp continuous_fst).prodMk (unitsLowerHomeomorph.continuous.comp continuous_snd)))

@[simp] theorem sectionGL_standard : sectionGL (r := r) (0, 1) = 1 := by
  have h : unitsLower (1 : ℝˣ) = 1 := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    fin_cases i
    fin_cases j
    simp [unitsLower, unitsGL]
  change lowerBlockPair (1 : G r) (rowEquiv 0) (unitsLower 1) = 1
  rw [h, show rowEquiv (n := r) 0 = 0 from rfl,
    Langlands.RankinSelberg.InducedTailIntermediate.lowerBlockPair_zero_one]
  change (rankInclusion 1) (1 : G r) = 1
  exact map_one _

theorem lastRow_lowerBlock (g : G r) (z : Z r) :
    lastRow (lowerBlockPair g (rowEquiv z.1) (unitsLower z.2)) = row z := by
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · change (lowerBlockPair g (rowEquiv z.1) (unitsLower z.2))
      ((0 : Fin 1).natAdd (r + 1)) ((0 : Fin 1).natAdd (r + 1)) = _
    rw [lowerBlockPair_22, row, Fin.snoc_last]
    simp [unitsLower, unitsGL]
  · change (lowerBlockPair g (rowEquiv z.1) (unitsLower z.2))
      ((0 : Fin 1).natAdd (r + 1)) (i.castAdd 1) = _
    rw [lowerBlockPair_21, row, Fin.snoc_castSucc]
    rfl

/-- The smaller quotient measure with the determinant density of the last-row chart. -/
def fiberMeasure (D : RealQuotientMeasureData r) : Measure (Q r) :=
  D.measure.withDensity (quotientDensity r)

instance (D : RealQuotientMeasureData r) : SigmaFinite (fiberMeasure D) := by
  let := ArchimedeanRealPairIdentity.sigmaFinite_measure D
  exact SigmaFinite.withDensity_of_ne_top' fun _ => ENNReal.ofReal_ne_top

/-- The integral in the leading block at the supplied last row. -/
def fiber (D : RealQuotientMeasureData r) (F : G (r + 1) → ℂ) (z : Z r) : ℂ :=
  ∫ q, F (rankInclusion 1 q.out * sectionGL z) ∂fiberMeasure D

/-- The product of Lebesgue measure on the initial entries and multiplicative Haar measure
on the last coordinate. -/
def rowMeasure (r : ℕ) : Measure (Z r) := volume.prod RealRankZero.unitsHaar

instance (r : ℕ) : SigmaFinite (rowMeasure r) := inferInstanceAs
  (SigmaFinite (volume.prod RealRankZero.unitsHaar : Measure (Z r)))

private theorem quotient_eval {n : ℕ} {A : Type*} (F : G n → A)
    (hF : ∀ u : N n, ∀ g, F (u.val * g) = F g) (g : G n) :
    F ((Quotient.mk _ g : Q n).out) = F g :=
  congrArg (descend _ F hF) (Quotient.out_eq (Quotient.mk _ g : Q n))

private theorem chart_eval {A : Type*} (F : G (r + 1) → A)
    (hF : ∀ u : N (r + 1), ∀ g, F (u.val * g) = F g) (q : Q r) (z : Z r) :
    F (lastRowChart r (q, z)).out = F (rankInclusion 1 q.out * sectionGL z) := by
  have h := lowerBlockQuotientChart_mk q.out (rowEquiv z.1) (unitsLower z.2)
  rw [Quotient.out_eq] at h
  change lastRowChart r (q, z) = (Quotient.mk _ _ : Q (r + 1)) at h
  rw [h, quotient_eval F hF, sectionGL, rankInclusion_mul_lowerBlockPair, mul_one]

private theorem chart_row (q : Q r) (z : Z r) :
    lastRow (lastRowChart r (q, z)).out = row z := by
  rw [chart_eval lastRow (fun u g => lastRow_unipotent_mul u g), sectionGL,
    rankInclusion_mul_lowerBlockPair, mul_one, lastRow_lowerBlock]

/-- Integrating a bounded function of the last row first integrates the invariant coefficient
in the leading block and then uses the product measure in the row coordinates. -/
theorem integral_lastRow (D : RealQuotientMeasureData r) (E : RealQuotientMeasureData (r + 1))
    (F : G (r + 1) → ℂ) (hFc : Continuous F)
    (hF : ∀ u : N (r + 1), ∀ g, F (u.val * g) = F g)
    (hFi : Integrable (fun q => F q.out) E.measure) :
    ∃ C : ℝ, 0 < C ∧ Integrable (fiber D F) (rowMeasure r) ∧
      ∀ (Θ : Row (r + 1) → ℂ), Measurable Θ → (∀ η, ‖Θ η‖ ≤ 1) →
        (∫ q : Q (r + 1), Θ (lastRow q.out) * F q.out ∂E.measure) =
          (C : ℂ) * ∫ z, Θ (row z) * fiber D F z ∂rowMeasure r := by
  obtain ⟨C, hC, hchart⟩ := lastRowChart_integral D E
  have hFm : Measurable (fun q : Q (r + 1) => F q.out) := by
    simp_rw [RealEqualConvergence.out_eq_descend F hF]
    exact (RealEqualConvergence.continuous_descend hF hFc).measurable
  have hrowc : Continuous (fun q : Q (r + 1) => lastRow q.out) := by
    apply (leftQuotient_isOpenQuotientMap (N (r + 1))).isQuotientMap.continuous_iff.mpr
    have he : (fun q : Q (r + 1) => lastRow q.out) ∘ leftQuotientMap (N (r + 1)) =
        (lastRow : G (r + 1) → Row (r + 1)) :=
      funext (quotient_eval lastRow (fun u g => lastRow_unipotent_mul u g))
    rw [he]
    have hv : Continuous (fun g : G (r + 1) =>
        (g.val : Matrix (Fin (r + 2)) (Fin (r + 2)) ℝ)) := Units.continuous_val
    exact continuous_pi fun j => (continuous_apply_apply _ j).comp hv
  have hcomp := ((hchart _ hFm).1.mp hFi).congr (ae_of_all _ fun z => chart_eval F hF z.1 z.2)
  have hcomp' : Integrable (fun p : Q r × Z r => F (rankInclusion 1 p.1.out * sectionGL p.2))
      ((fiberMeasure D).prod (rowMeasure r)) := hcomp
  refine ⟨C, hC, hcomp'.integral_prod_right, fun Θ hΘ hb => ?_⟩
  let Ψ := fun q : Q (r + 1) => Θ (lastRow q.out) * F q.out
  have hΨ : Measurable Ψ := (hΘ.comp hrowc.measurable).mul hFm
  have hΨi : Integrable Ψ E.measure := by
    refine hFi.norm.mono' hΨ.aestronglyMeasurable (ae_of_all _ fun q => ?_)
    change ‖Θ (lastRow q.out) * F q.out‖ ≤ ‖F q.out‖
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hb _)
  have he (p : Q r × Z r) : Ψ (lastRowChart r p) =
      Θ (row p.2) * F (rankInclusion 1 p.1.out * sectionGL p.2) := by
    change Θ (lastRow (lastRowChart r (p.1, p.2)).out) *
      F (lastRowChart r (p.1, p.2)).out = _
    rw [chart_row, chart_eval F hF]
  have hi := ((hchart Ψ hΨ).1.mp hΨi).congr (ae_of_all _ he)
  calc
    _ = (C : ℂ) * ∫ p : Q r × Z r, Ψ (lastRowChart r p) ∂lastRowMeasure r D := (hchart Ψ hΨ).2
    _ = (C : ℂ) * ∫ p : Q r × Z r,
        Θ (row p.2) * F (rankInclusion 1 p.1.out * sectionGL p.2) ∂lastRowMeasure r D :=
      congrArg ((C : ℂ) * ·) (integral_congr_ae (ae_of_all _ he))
    _ = _ := by
      change (C : ℂ) * ∫ p : Q r × Z r,
        Θ (row p.2) * F (rankInclusion 1 p.1.out * sectionGL p.2)
        ∂(fiberMeasure D).prod (rowMeasure r) = _
      rw [integral_prod_symm (μ := fiberMeasure D) (ν := rowMeasure r) _ hi]
      simp_rw [integral_const_mul, fiber]

private def splitRow (r : ℕ) : Row (r + 1) ≃ᵐ (Row r × ℝ) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (r + 2) => ℝ) (Fin.last (r + 1))).trans
    (MeasurableEquiv.prodComm : ℝ × Row r ≃ᵐ Row r × ℝ)

private theorem splitRow_preserving :
    MeasurePreserving (splitRow r)
      (volume : Measure (Row (r + 1))) (volume.prod volume) := by
  have h := volume_preserving_piFinSuccAbove (fun _ : Fin (r + 2) => ℝ) (Fin.last (r + 1))
  exact measurePreserving_swap.comp h

private theorem splitRow_apply (η : Row (r + 1)) :
    splitRow r η = ((fun j => η j.castSucc), η (Fin.last (r + 1))) := by
  simp [splitRow, Fin.insertNthEquiv]
  rfl

private def rowInclusion (z : Z r) : Row r × ℝ := (z.1, z.2)

private theorem openEmbedding_rowInclusion : IsOpenEmbedding (rowInclusion (r := r)) :=
  IsOpenEmbedding.id.prodMap Units.isOpenEmbedding_val

private theorem splitRow_row (z : Z r) : splitRow r (row z) = rowInclusion z := by
  simp [splitRow_apply, row, rowInclusion]

private theorem map_rowInclusion :
    (rowMeasure r).map rowInclusion =
      (volume.prod (volume : Measure ℝ)).withDensity
        (fun z => (RealRankZero.invAbs z.2 : ℝ≥0∞)) := by
  change (volume.prod RealRankZero.unitsHaar).map (Prod.map id Units.val) = _
  rw [← Measure.map_prod_map _ _ measurable_id Units.continuous_val.measurable, Measure.map_id,
    RealRankZero.map_val_unitsHaar, RealRankZero.invAbsVolume,
    prod_withDensity_right RealRankZero.measurable_invAbs.coe_nnreal_ennreal]

/-- The real Fourier character associated to a row and a frequency row. -/
def rowCharacter {m : ℕ} (b η : Fin m → ℝ) : ℂ :=
  (Real.fourierChar (∑ i, η i * b i) : ℂ)

theorem norm_rowCharacter {m : ℕ} (b η : Fin m → ℝ) : ‖rowCharacter b η‖ = 1 :=
  (Real.fourierChar _).norm_coe

theorem continuous_rowCharacter {m : ℕ} (b : Fin m → ℝ) :
    Continuous (rowCharacter b) :=
  (continuous_subtype_val.comp Real.continuous_fourierChar).comp
    (continuous_finsetSum _ fun i _ => (continuous_apply i).mul_const _)

private theorem eq_zero_of_fourier_integrals {m : ℕ} {g : (Fin m → ℝ) → ℂ} (hi : Integrable g)
    {η : Fin m → ℝ} (hc : ContinuousAt g η)
    (hz : ∀ b : Fin m → ℝ, ∫ x, rowCharacter b x * g x = 0) : g η = 0 := by
  let E := EuclideanSpace ℝ (Fin m)
  let e : E ≃ᵐ (Fin m → ℝ) := (MeasurableEquiv.toLp 2 (Fin m → ℝ)).symm
  have he : MeasurePreserving e := PiLp.volume_preserving_ofLp (Fin m)
  let f := g ∘ e
  have hF : 𝓕 f = 0 := by
    funext w
    rw [Real.fourier_eq, Pi.zero_apply]
    have hchar (v : E) : 𝐞 (-⟪v, w⟫) • f v = rowCharacter (fun i => -e w i) (e v) * g (e v) := by
      rw [Circle.smul_def, rowCharacter, PiLp.inner_apply, ← Finset.sum_neg_distrib]
      congr 3
      apply Finset.sum_congr rfl
      intro i _
      simp [e, RCLike.inner_apply, mul_comm]
      rfl
    simp_rw [hchar]
    exact (he.integral_comp e.measurableEmbedding _).trans (hz _)
  have hfc : ContinuousAt f (e.symm η) := by
    have h : ContinuousAt g (e (e.symm η)) := by simpa using hc
    exact h.comp (PiLp.continuous_ofLp 2 (fun _ : Fin m => ℝ)).continuousAt
  have hf : Integrable f := (he.integrable_comp_emb e.measurableEmbedding).mpr hi
  have hinv := hf.fourierInv_fourier_eq (by rw [hF]; exact integrable_zero _ _ _) hfc
  rw [hF] at hinv
  simpa [f, Real.fourierInv_eq] using hinv.symm

/-- An integrable last-row density that is continuous at the standard row vanishes there
if all of its real Fourier moments vanish. -/
theorem eq_zero_of_row_integrals {f : Z r → ℂ} (hi : Integrable f (rowMeasure r))
    (hc : ContinuousAt f (0, 1))
    (hz : ∀ b : Row (r + 1), (∫ z, rowCharacter b (row z) * f z ∂rowMeasure r) = 0) :
    f (0, 1) = 0 := by
  let F (p : Row r × ℝ) := if h : p.2 ≠ 0 then f (p.1, Units.mk0 p.2 h) else 0
  have hF (z : Z r) : F (rowInclusion z) = f z := by
    have he : Units.mk0 (z.2 : ℝ) z.2.ne_zero = z.2 := Units.ext rfl
    simp [F, rowInclusion, z.2.ne_zero, he]
  let d : Row r × ℝ → ℝ≥0 := fun p => RealRankZero.invAbs p.2
  let g := fun p => (d p : ℂ) * F p
  have hd : Measurable d := RealRankZero.measurable_invAbs.comp measurable_snd
  have hEmb := (openEmbedding_rowInclusion (r := r)).measurableEmbedding
  have hgi : Integrable g (volume.prod volume) := by
    have h := hi.congr (ae_of_all _ fun z => (hF z).symm)
    have h1 := (hEmb.integrable_map_iff (μ := rowMeasure r) (g := F)).mpr h
    rw [map_rowInclusion] at h1
    have h2 := (integrable_withDensity_iff_integrable_smul (μ := volume.prod volume) hd).mp h1
    simpa only [g, NNReal.smul_def, Complex.real_smul] using h2
  have hg (b : Row (r + 1)) :
      ∫ p, rowCharacter b ((splitRow r).symm p) * g p ∂volume.prod volume = 0 := by
    rw [show (fun p => rowCharacter b ((splitRow r).symm p) * g p) =
        fun p => d p • (rowCharacter b ((splitRow r).symm p) * F p) from by
      funext p
      simp only [g, NNReal.smul_def, Complex.real_smul]
      ring,
      ← integral_withDensity_eq_integral_smul hd, ← map_rowInclusion,
      hEmb.integral_map]
    refine (integral_congr_ae (ae_of_all _ fun z => ?_)).trans (hz b)
    rw [← splitRow_row z, MeasurableEquiv.symm_apply_apply, splitRow_row, hF]
  have hgc : ContinuousAt g (0, 1) := by
    have hFc : ContinuousAt F (0, 1) := by
      rw [show ((0, 1) : Row r × ℝ) = rowInclusion (0, 1) from rfl,
        ← (openEmbedding_rowInclusion (r := r)).continuousAt_iff]
      simpa only [Function.comp_def, hF] using hc
    have hd₁ : ContinuousAt (fun p : Row r × ℝ => (d p : ℂ)) (0, 1) :=
      Complex.continuous_ofReal.continuousAt.comp
        ((continuous_snd.norm.continuousAt).inv₀ (by simp))
    exact hd₁.mul hFc
  let η := row (r := r) (0, 1)
  have he : splitRow r η = (0, 1) := splitRow_row _
  have hcont : Continuous (splitRow r : Row (r + 1) → Row r × ℝ) := by
    rw [show (splitRow r : Row (r + 1) → Row r × ℝ) =
      fun y => ((fun j => y j.castSucc), y (Fin.last (r + 1))) from funext splitRow_apply]
    exact (continuous_pi fun i => continuous_apply i.castSucc).prodMk (continuous_apply _)
  have h := eq_zero_of_fourier_integrals (g := g ∘ splitRow r)
    ((splitRow_preserving (r := r)).integrable_comp_emb (splitRow r).measurableEmbedding |>.mpr hgi)
    (hgc.comp_of_eq hcont.continuousAt he) fun b => by
      have hp := (splitRow_preserving (r := r)).integral_comp (splitRow r).measurableEmbedding
        (fun p => rowCharacter b ((splitRow r).symm p) * g p)
      simpa only [Function.comp_def, MeasurableEquiv.symm_apply_apply] using hp.trans (hg b)
  change g (splitRow r η) = 0 at h
  rw [show splitRow r η = rowInclusion (0, 1) from splitRow_row _] at h
  change (d (rowInclusion (0, 1)) : ℂ) * F (rowInclusion (0, 1)) = 0 at h
  rw [hF] at h
  simpa [d, rowInclusion, RealRankZero.invAbs] using h

/-- Vanishing of all last-row Fourier moments of a continuous invariant coefficient forces
its leading-block integral at the standard row to vanish, when that integral is continuous
at the standard row. -/
def RealOrdinaryRowLocalizationStatement : Prop :=
  ∀ (r : ℕ) (D : RealQuotientMeasureData r) (E : RealQuotientMeasureData (r + 1))
    (F : G (r + 1) → ℂ), Continuous F →
    (∀ u : N (r + 1), ∀ g, F (u.val * g) = F g) →
    Integrable (fun q => F q.out) E.measure →
    ContinuousAt (fiber D F) (0, 1) →
    (∀ b : Row (r + 1),
      (∫ q : Q (r + 1), rowCharacter b (lastRow q.out) * F q.out ∂E.measure) = 0) →
    fiber D F (0, 1) = 0

theorem realOrdinaryRowLocalization : RealOrdinaryRowLocalizationStatement := by
  intro r D E F hc hN hi hFiber hz
  obtain ⟨c, hc₀, hInt, h⟩ := integral_lastRow D E F hc hN hi
  refine eq_zero_of_row_integrals hInt hFiber fun b => ?_
  have hs := h (rowCharacter b) (continuous_rowCharacter b).measurable
    (fun η => (norm_rowCharacter b η).le)
  rw [hz b] at hs
  exact (mul_eq_zero.mp hs.symm).resolve_left (Complex.ofReal_ne_zero.mpr hc₀.ne')

end Langlands.Global.RankinSelbergGlobal.RealOrdinaryRowLocalization
