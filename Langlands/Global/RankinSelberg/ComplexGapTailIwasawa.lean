import Langlands.Global.RankinSelberg.ComplexGodementTriangularIntegral
import Langlands.Global.RankinSelberg.ComplexJacquetUnipotentMeasure
import Langlands.Representation.Archimedean.ComplexGeneralLinearHaarDensity
import Langlands.Representation.GodementJacquet.ComplexMatrixHaar
import Mathlib.MeasureTheory.Measure.WithDensity

/-! # Haar measure in the triangular tail of the unequal-rank chart -/

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGapTailIwasawa

open Langlands.Archimedean (unitaryCompact)
open Langlands.Archimedean.ComplexGeneralLinearHaarDensity (complexGeneralLinearHaar)
open Langlands.GeneralLinear (UpperEntryPair upperEntryCoordinates upperEntryProductMeasure)
open Langlands.GodementJacquet (complexAbsHom continuous_complexAbsHom map_complex_mul_addHaar)
open Langlands.HarmonicAnalysis (AdditiveHaarMeasure pi_nnreal_smul)
open ComplexGodement (exists_rightIwasawa_entryMeasure)
open ComplexJacquetUnipotentMeasure (entryHaar entryHaar_sigmaFinite)
open ComplexLocalIwasawa (conjTorus conjTorus_val continuous_conjTorus continuous_logTorus logTorus_neg)
open ComplexLocalWhittakerGauge (logTorus logTorus_inv_val logTorus_val)

variable {q : ℕ}

local notation "G" => Langlands.GeneralLinear (q + 1) ℂ
local notation "N" => Langlands.GeneralLinear.upperUnipotent (q + 1) ℂ
local notation "Compact" => unitaryCompact ℂ (q + 1)
local notation "Y" => Fin (q + 1) → ℝ
local notation "X" => UpperEntryPair (q + 1) → ℂ
local notation "Coords" => (Y × N) × Compact

local instance tailGLMeasurable (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear n ℂ) := borel _
local instance tailGLBorel (n : ℕ) : BorelSpace (Langlands.GeneralLinear n ℂ) := ⟨rfl⟩
local instance tailGLSecondCountable (n : ℕ) : SecondCountableTopology (Langlands.GeneralLinear n ℂ) :=
  Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology
local instance tailNMeasurable : MeasurableSpace N := borel _
local instance tailNBorel : BorelSpace N := ⟨rfl⟩

private def rootRatio (y : Y) (ij : UpperEntryPair (q + 1)) : ℂ :=
  (Real.exp (y ij.val.2 - y ij.val.1) : ℂ)

private theorem rootRatio_ne_zero (y : Y) (ij : UpperEntryPair (q + 1)) : rootRatio y ij ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)

/-- Tail modulus for moving a positive diagonal matrix left of upper unipotents. -/
def tailModulus (y : Y) : ℝ≥0 :=
  ∏ ij : UpperEntryPair (q + 1), (complexAbsHom (rootRatio y ij))⁻¹

/-- All tail root factors, including the empty product, give a positive modulus. -/
theorem tailModulus_pos (y : Y) : 0 < tailModulus y := by
  apply Finset.prod_pos
  intro ij _
  rw [inv_pos]
  change 0 < ‖rootRatio y ij‖₊ ^ 2
  exact pow_pos (nnnorm_pos.mpr (rootRatio_ne_zero y ij)) _

theorem measurable_tailModulus : Measurable (fun y : Y => (tailModulus y : ℝ≥0∞)) := by
  apply Measurable.coe_nnreal_ennreal
  unfold tailModulus
  apply Finset.measurable_prod
  intro ij _
  apply Measurable.inv
  have hi : Continuous (fun y : Y => y ij.val.1) := continuous_apply ij.val.1
  have hj : Continuous (fun y : Y => y ij.val.2) := continuous_apply ij.val.2
  exact continuous_complexAbsHom.measurable.comp
    (Complex.continuous_ofReal.comp (Real.continuous_exp.comp (hj.sub hi))).measurable

private theorem conjugate_entry (y : Y) (u : N) (ij : UpperEntryPair (q + 1)) :
    upperEntryCoordinates (q + 1) (conjTorus (-y) u) ij =
      rootRatio y ij * upperEntryCoordinates (q + 1) u ij := by
  simp only [Langlands.GeneralLinear.upperEntryCoordinates_apply]
  change (conjTorus (-y) u : G).val ij.val.1 ij.val.2 = _
  rw [conjTorus_val, logTorus_neg, inv_inv]
  simp only [Units.val_mul, logTorus_inv_val, logTorus_val, Matrix.mul_diagonal, Matrix.diagonal_mul,
    rootRatio, sub_eq_add_neg, Real.exp_add, Complex.ofReal_mul]
  ring

private theorem map_scaleEntries (μ : AdditiveHaarMeasure ℂ) (y : Y) :
    (upperEntryProductMeasure μ (q + 1)).map (fun x : X => fun ij => rootRatio y ij * x ij) =
      tailModulus y • upperEntryProductMeasure μ (q + 1) := by
  let : μ.measure.IsAddHaarMeasure := μ.isAddHaar
  let : SigmaFinite μ.measure := inferInstance
  let f := fun x : X => fun ij => rootRatio y ij * x ij
  have hmap (ij : UpperEntryPair (q + 1)) := map_complex_mul_addHaar μ.measure (rootRatio_ne_zero y ij)
  let ν := Measure.pi fun _ : UpperEntryPair (q + 1) => μ.measure
  change ν.map f = tailModulus y • ν
  have hs : ∀ ij : UpperEntryPair (q + 1), SigmaFinite
      (μ.measure.map (fun z => rootRatio y ij * z)) := by
    intro ij
    rw [hmap ij]
    infer_instance
  have he : ν.map f = Measure.pi (fun ij : UpperEntryPair (q + 1) =>
      ((complexAbsHom (rootRatio y ij))⁻¹ : ℝ≥0) • μ.measure) := by
    rw [show ν.map f = Measure.pi (fun ij : UpperEntryPair (q + 1) =>
        μ.measure.map (fun z => rootRatio y ij * z)) from
      Measure.pi_map_pi (μ := fun _ : UpperEntryPair (q + 1) => μ.measure)
        (f := fun ij z => rootRatio y ij * z) (hμ := hs)
        (fun ij => (measurable_const.mul measurable_id).aemeasurable)]
    simp_rw [hmap]
  rw [he]
  exact pi_nnreal_smul (fun _ : UpperEntryPair (q + 1) => μ.measure)
    (fun ij => (complexAbsHom (rootRatio y ij))⁻¹)

private theorem map_tailConjugation (μ : AdditiveHaarMeasure ℂ) (y : Y) :
    (entryHaar μ (q + 1)).map (conjTorus (-y)) = tailModulus y • entryHaar μ (q + 1) := by
  let e := upperEntryCoordinates (K := ℂ) (q + 1)
  have hEq : conjTorus (-y) ∘ e.symm = e.symm ∘ (fun x : X => fun ij => rootRatio y ij * x ij) := by
    funext x
    apply e.injective
    funext ij
    change e (conjTorus (-y) (e.symm x)) ij = e (e.symm _) ij
    rw [e.apply_symm_apply, conjugate_entry]
    change rootRatio y ij * e (e.symm x) ij = rootRatio y ij * x ij
    rw [e.apply_symm_apply]
  have hScale : Measurable (fun x : X => fun ij => rootRatio y ij * x ij) :=
    Measurable.of_eval fun ij => measurable_const.mul (measurable_pi_apply ij)
  unfold entryHaar
  change ((upperEntryProductMeasure μ (q + 1)).map e.symm).map _ = _
  rw [Measure.map_map (continuous_conjTorus (-y)).measurable e.symm.measurable, hEq,
    ← Measure.map_map e.symm.measurable hScale, map_scaleEntries,
    Measure.map_smul _ e.symm.measurable.aemeasurable]

private def shear (p : Y × N) : Y × N := (p.1, conjTorus (-p.1) p.2)

private theorem measurable_shear : Measurable (shear (q := q)) := by
  apply measurable_fst.prodMk
  apply Continuous.measurable
  apply Continuous.subtype_mk
  change Continuous (fun p : Y × N => (conjTorus (-p.1) p.2).val)
  simp only [conjTorus_val, logTorus_neg, inv_inv]
  have ht : Continuous (fun p : Y × N => logTorus p.1) := continuous_logTorus.comp continuous_fst
  exact (ht.inv.mul (continuous_subtype_val.comp continuous_snd)).mul ht

/-- The logarithmic diagonal measure with the triangular tail modulus. -/
def tailDiagonalMeasure (q : ℕ) : Measure (Fin (q + 1) → ℝ) :=
  volume.withDensity (fun y => (tailModulus y : ℝ≥0∞))

instance (q : ℕ) : SigmaFinite (tailDiagonalMeasure q) :=
  SigmaFinite.withDensity tailModulus

private theorem measurePreserving_shear (μ : AdditiveHaarMeasure ℂ) :
    MeasurePreserving (shear (q := q)) (volume.prod (entryHaar μ (q + 1)))
      ((tailDiagonalMeasure q).prod (entryHaar μ (q + 1))) := by
  let ν := entryHaar μ (q + 1)
  let : SigmaFinite ν := entryHaar_sigmaFinite μ _
  refine ⟨measurable_shear, Measure.ext_of_lintegral _ fun F hF => ?_⟩
  rw [lintegral_map hF measurable_shear]
  change (∫⁻ p, (F ∘ shear) p ∂volume.prod ν) = ∫⁻ p, F p ∂(tailDiagonalMeasure q).prod ν
  rw [lintegral_prod _ (hF.comp measurable_shear).aemeasurable, lintegral_prod _ hF.aemeasurable,
    tailDiagonalMeasure,
    lintegral_withDensity_eq_lintegral_mul _ measurable_tailModulus hF.lintegral_prod_right']
  apply lintegral_congr
  intro y
  change (∫⁻ z, F (y, conjTorus (-y) z) ∂ν) = (tailModulus y : ℝ≥0∞) * ∫⁻ z, F (y, z) ∂ν
  have hy : Measurable (fun z : N => F (y, z)) := hF.comp (measurable_const.prodMk measurable_id)
  rw [← lintegral_map hy (continuous_conjTorus (-y)).measurable,
    show ν.map (conjTorus (-y)) = tailModulus y • ν from map_tailConjugation μ y, lintegral_smul_measure]
  rfl

/-- The tail block factorization in compact, positive diagonal, upper unipotent order. -/
def tailChart (p : Coords) : G := p.2.val * logTorus p.1.1 * p.1.2.val

theorem continuous_tailChart : Continuous (tailChart (q := q)) :=
  ((continuous_subtype_val.comp continuous_snd).mul
    (continuous_logTorus.comp (continuous_fst.comp continuous_fst))).mul
      (continuous_subtype_val.comp (continuous_snd.comp continuous_fst))

/-- The triangular tail chart expresses complex group Haar as the product of the
logarithmic diagonal measure, entry-product Haar and compact Haar up to one constant. -/
def ComplexGapTailIwasawaStatement : Prop :=
  ∀ (q : ℕ) (μ : AdditiveHaarMeasure ℂ) (κ : Measure (unitaryCompact ℂ (q + 1))),
    κ.IsHaarMeasure → ∃ c : ℝ≥0, 0 < c ∧
    complexGeneralLinearHaar (q + 1) = c •
      (((tailDiagonalMeasure q).prod (entryHaar μ (q + 1))).prod κ).map tailChart

set_option maxHeartbeats 800000 in
private theorem tailIwasawa (μ : AdditiveHaarMeasure ℂ) (κ : Measure Compact) (hκ : κ.IsHaarMeasure) :
    ∃ c : ℝ≥0, 0 < c ∧ complexGeneralLinearHaar (q + 1) = c •
      (((tailDiagonalMeasure q).prod (entryHaar μ (q + 1))).prod κ).map tailChart := by
  let Haar := complexGeneralLinearHaar (q + 1)
  let : κ.IsHaarMeasure := hκ
  let : Haar.IsHaarMeasure := inferInstance
  let : Haar.IsMulRightInvariant := inferInstance
  obtain ⟨c, hc, hRight⟩ := exists_rightIwasawa_entryMeasure Haar κ
  let e := (upperEntryCoordinates (K := ℂ) (q + 1)).symm
  let ν := entryHaar μ (q + 1)
  let : SigmaFinite ν := entryHaar_sigmaFinite μ _
  let : SecondCountableTopology N := e.symm.secondCountableTopology
  let : SecondCountableTopology Compact := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  let ξ := upperEntryProductMeasure μ (q + 1)
  let : μ.measure.IsAddHaarMeasure := μ.isAddHaar
  let : SigmaFinite μ.measure := inferInstance
  let : ξ.IsAddHaarMeasure := inferInstance
  let b := Measure.addHaarScalarFactor (volume : Measure X) ξ
  have hb : 0 < b := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _
  have hVol : (volume : Measure X) = b • ξ := Measure.isAddLeftInvariant_eq_smul _ _
  let source := ((volume : Measure Y).prod ξ).prod κ
  let entryChart (p : (Y × X) × Compact) : G := p.2.val * (e p.1.2).val * logTorus p.1.1
  have hEntryChart : Measurable entryChart :=
    (((continuous_subtype_val.comp continuous_snd).mul
      (continuous_subtype_val.comp (e.continuous.comp (continuous_snd.comp continuous_fst)))).mul
      (continuous_logTorus.comp (continuous_fst.comp continuous_fst))).measurable
  let fromEntries := Prod.map (Prod.map (id : Y → Y) e) (id : Compact → Compact)
  have hFromEntries : MeasurePreserving fromEntries source ((volume.prod ν).prod κ) :=
    ((MeasurePreserving.id _).prod (show MeasurePreserving e ξ ν from ⟨e.measurable, rfl⟩)).prod
      (MeasurePreserving.id _)
  let S := Prod.map (shear (q := q)) (id : Compact → Compact)
  have hChange : MeasurePreserving (S ∘ fromEntries) source (((tailDiagonalMeasure q).prod ν).prod κ) :=
    ((measurePreserving_shear μ).prod (MeasurePreserving.id κ)).comp hFromEntries
  have hChart : entryChart = tailChart ∘ (S ∘ fromEntries) := by
    funext p
    change p.2.val * (e p.1.2).val * logTorus p.1.1 =
      p.2.val * logTorus p.1.1 * (conjTorus (-p.1.1) (e p.1.2)).val
    simp only [conjTorus_val, logTorus_neg, inv_inv, mul_assoc, mul_inv_cancel_left]
  change Haar = c • (((volume : Measure Y).prod (volume : Measure X)).prod κ).map entryChart at hRight
  refine ⟨c * b, mul_pos hc hb, ?_⟩
  change Haar = (c * b) • (((tailDiagonalMeasure q).prod ν).prod κ).map tailChart
  rw [hRight, hVol, Measure.prod_smul_right, Measure.prod_smul_left,
    Measure.map_smul _ hEntryChart.aemeasurable, smul_smul, hChart,
    ← Measure.map_map continuous_tailChart.measurable hChange.measurable, hChange.map_eq]

theorem complexGapTailIwasawa : ComplexGapTailIwasawaStatement :=
  fun _ μ κ hκ => tailIwasawa μ κ hκ

end Langlands.Global.RankinSelbergGlobal.ComplexGapTailIwasawa
