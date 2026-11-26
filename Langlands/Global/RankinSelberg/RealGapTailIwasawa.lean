import Langlands.Global.RankinSelberg.RealLocalIwasawaHaar
import Langlands.Global.RankinSelberg.RealIwasawaMeasure
import Langlands.Global.RankinSelberg.RealGodementHaar
import Langlands.Global.RankinSelberg.RealJacquetUnipotentMeasure
import Langlands.Group.GL.UpperUnipotentEntryCoordinates
import Langlands.HarmonicAnalysis.TriangularTranslationProof
import Langlands.Analysis.Local.CompactFactorizationHaar
import Mathlib.MeasureTheory.Measure.WithDensity

/-! # Haar measure in the triangular tail of the real unequal-rank chart -/

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGapTailIwasawa

open Langlands.Archimedean (unitaryCompact)
open Langlands.GeneralLinear (UpperEntryPair upperEntryCoordinates upperEntryCoordinates_mul
  upperEntryProductMeasure)
open Langlands.HarmonicAnalysis (AdditiveHaarMeasure pi_nnreal_smul)
open RealJacquetUnipotentMeasure (entryHaar entryHaar_sigmaFinite)
open RealIwasawa (conjTorus torus torus_neg torus_val continuous_torus)
open RealLocalIwasawaHaar (realIwasawaHaar)

variable {q : ℕ}

local notation "G" => Langlands.GeneralLinear (q + 1) ℝ
local notation "N" => Langlands.GeneralLinear.upperUnipotent (q + 1) ℝ
local notation "Compact" => unitaryCompact ℝ (q + 1)
local notation "Y" => Fin (q + 1) → ℝ
local notation "X" => UpperEntryPair (q + 1) → ℝ
local notation "Coords" => (Y × N) × Compact

local instance tailGLMeasurable (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear n ℝ) := borel _
local instance tailGLBorel (n : ℕ) : BorelSpace (Langlands.GeneralLinear n ℝ) := ⟨rfl⟩
local instance tailGLSecondCountable (n : ℕ) : SecondCountableTopology (Langlands.GeneralLinear n ℝ) :=
  Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology
local instance tailNMeasurable : MeasurableSpace N := borel _
local instance tailNBorel : BorelSpace N := ⟨rfl⟩

section RightIwasawa

variable {n : ℕ}
local notation "G'" => Langlands.GeneralLinear n ℝ
local notation "N'" => Langlands.GeneralLinear.upperUnipotent n ℝ
local notation "K'" => unitaryCompact ℝ n
local notation "Y'" => (Fin n → ℝ)
local notation "X'" => (UpperEntryPair n → ℝ)

private theorem entryCorrection_right_depends (a : N') (ij : UpperEntryPair n) (x z : X')
    (he : ∀ kl : UpperEntryPair n,
      kl.1.2.val - kl.1.1.val < ij.1.2.val - ij.1.1.val → x kl = z kl) :
    (upperEntryCoordinates n ((upperEntryCoordinates n).symm x * a) - x) ij =
      (upperEntryCoordinates n ((upperEntryCoordinates n).symm z * a) - z) ij := by
  simp only [Pi.sub_apply, upperEntryCoordinates_mul, Homeomorph.apply_symm_apply]
  have hs :
      (∑ k : {k : Fin n // ij.1.1 < k ∧ k < ij.1.2},
        x ⟨(ij.1.1, k), k.2.1⟩ * upperEntryCoordinates n a ⟨(k, ij.1.2), k.2.2⟩) =
      ∑ k : {k : Fin n // ij.1.1 < k ∧ k < ij.1.2},
        z ⟨(ij.1.1, k), k.2.1⟩ * upperEntryCoordinates n a ⟨(k, ij.1.2), k.2.2⟩ := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [he ⟨(ij.1.1, k), k.2.1⟩]
    have hi : ij.1.1.val < k.val.val := k.2.1
    have hj : k.val.val < ij.1.2.val := k.2.2
    dsimp
    omega
  rw [hs]
  abel

private theorem upperEntry_rightTranslation_preserving (a : N') :
    MeasurePreserving (fun x : X' => upperEntryCoordinates n ((upperEntryCoordinates n).symm x * a))
      volume volume := by
  let f : X' → X' := fun x => upperEntryCoordinates n ((upperEntryCoordinates n).symm x * a) - x
  have hf : Continuous f :=
    ((upperEntryCoordinates n).continuous.comp
      ((upperEntryCoordinates n).symm.continuous.mul continuous_const)).sub continuous_id
  have hp := Langlands.HarmonicAnalysis.finiteTriangularTranslation
    (UpperEntryPair n) (fun _ => ℝ) (fun _ => volume)
    (fun ij => ij.1.2.val - ij.1.1.val) f hf.measurable (entryCorrection_right_depends a)
  have he : (fun x ij => f x ij + x ij) =
      fun x => upperEntryCoordinates n ((upperEntryCoordinates n).symm x * a) := by
    funext x ij
    exact sub_add_cancel _ _
  rw [he] at hp
  exact hp

private theorem rightInvariant_entryHaar :
    ((volume : Measure X').map (upperEntryCoordinates n).symm).IsMulRightInvariant := by
  let e : N' ≃ₜ X' := upperEntryCoordinates n
  refine ⟨fun a => ?_⟩
  have hp := upperEntry_rightTranslation_preserving a
  have he : (· * a) ∘ e.symm = e.symm ∘ (fun x => e (e.symm x * a)) := by
    funext x
    exact (e.symm_apply_apply _).symm
  rw [Measure.map_map (measurable_mul_const a) e.symm.measurable, he,
    ← Measure.map_map e.symm.measurable hp.measurable, hp.map_eq]

/-- The right Haar formula in unitary, unipotent, positive-diagonal order, with additive
Lebesgue measure in the unipotent entries and in the logarithmic diagonal coordinates. -/
private theorem exists_rightIwasawa_entryMeasure (μ : Measure G') [μ.IsHaarMeasure]
    [μ.IsMulRightInvariant] (κ : Measure K') [κ.IsHaarMeasure] :
    ∃ c : ℝ≥0, 0 < c ∧ μ = c • Measure.map
      (fun p : (Y' × X') × K' => p.2.val * ((upperEntryCoordinates n).symm p.1.2).val * torus p.1.1)
      (((volume : Measure Y').prod (volume : Measure X')).prod κ) := by
  let e : N' ≃ₜ X' := upperEntryCoordinates n
  let ν : Measure N' := (volume : Measure X').map e.symm
  have : ν.IsMulRightInvariant := rightInvariant_entryHaar
  have : IsFiniteMeasureOnCompacts ν := IsFiniteMeasureOnCompacts.map _ e.symm
  have : ν.IsOpenPosMeasure := e.symm.continuous.isOpenPosMeasure_map e.symm.surjective
  have : ν.inv.IsHaarMeasure := {}
  have : μ.inv.IsHaarMeasure := {}
  have : κ.IsMulRightInvariant := Langlands.CompactFactorization.isMulRightInvariant_of_compactSpace κ
  have : κ.inv.IsHaarMeasure := {}
  obtain ⟨c, hc, hμ⟩ := realIwasawaHaar n μ.inv ν.inv κ.inv inferInstance inferInstance inferInstance
  let toG : (Y' × N') × K' → G' := fun p => torus p.1.1 * p.1.2.val * p.2.val
  have htoG : Measurable toG :=
    ((RealIwasawa.continuous_torus.measurable.comp (measurable_fst.comp measurable_fst)).mul
      (measurable_subtype_coe.comp (measurable_snd.comp measurable_fst))).mul
      (measurable_subtype_coe.comp measurable_snd)
  let source := ((volume : Measure Y').prod (volume : Measure X')).prod κ
  let changeCoordinates : (Y' × X') × K' → (Y' × N') × K' :=
    Prod.map (Prod.map Neg.neg (fun x => (e.symm x)⁻¹)) Inv.inv
  have hiN : MeasurePreserving Inv.inv ν ν.inv := ⟨measurable_inv, rfl⟩
  have hiK : MeasurePreserving Inv.inv κ κ.inv := ⟨measurable_inv, rfl⟩
  have he : MeasurePreserving e.symm volume ν := ⟨e.symm.measurable, rfl⟩
  have hx : MeasurePreserving changeCoordinates source ((volume.prod ν.inv).prod κ.inv) :=
    ((Measure.measurePreserving_neg (volume : Measure Y')).prod (hiN.comp he)).prod hiK
  refine ⟨c, hc, ?_⟩
  calc
    μ = μ.inv.inv := (Measure.inv_inv μ).symm
    _ = c • Measure.map (Inv.inv ∘ toG ∘ changeCoordinates) source := by
      rw [Measure.inv_def, hμ, Measure.map_smul _ measurable_inv.aemeasurable,
        ← hx.map_eq, Measure.map_map htoG hx.measurable,
        Measure.map_map measurable_inv (htoG.comp hx.measurable)]
    _ = _ := by
      congr 2
      funext p
      change (torus (-p.1.1) * (e.symm p.1.2).val⁻¹ * p.2.val⁻¹)⁻¹ = _
      rw [torus_neg, mul_inv_rev, mul_inv_rev, inv_inv, inv_inv, inv_inv, mul_assoc]

end RightIwasawa

private def rootRatio (y : Y) (ij : UpperEntryPair (q + 1)) : ℝ :=
  Real.exp (y ij.val.2 - y ij.val.1)

private theorem rootRatio_ne_zero (y : Y) (ij : UpperEntryPair (q + 1)) : rootRatio y ij ≠ 0 :=
  Real.exp_ne_zero _

private theorem realHaar_map_mul (ν : Measure ℝ) [ν.IsAddHaarMeasure] (a : ℝ) (ha : a ≠ 0) :
    ν.map (fun x : ℝ => a * x) = (‖a‖₊)⁻¹ • ν := by
  change ν.map (fun x : ℝ => a • x) = _
  rw [Measure.map_addHaar_smul ν ha, Module.finrank_self, pow_one, abs_inv]
  rw [← Real.norm_eq_abs, ← coe_nnnorm, ← NNReal.coe_inv, ENNReal.ofReal_coe_nnreal]
  rfl

/-- Tail modulus for moving a positive diagonal matrix left of upper unipotents. -/
def tailModulus (y : Y) : ℝ≥0 :=
  ∏ ij : UpperEntryPair (q + 1), (‖rootRatio y ij‖₊)⁻¹

/-- All tail root factors, including the empty product, give a positive modulus. -/
theorem tailModulus_pos (y : Y) : 0 < tailModulus y := by
  apply Finset.prod_pos
  intro ij _
  rw [inv_pos]
  exact nnnorm_pos.mpr (rootRatio_ne_zero y ij)

theorem measurable_tailModulus : Measurable (fun y : Y => (tailModulus y : ℝ≥0∞)) := by
  apply Measurable.coe_nnreal_ennreal
  unfold tailModulus
  apply Finset.measurable_prod
  intro ij _
  apply Measurable.inv
  have hi : Continuous (fun y : Y => y ij.val.1) := continuous_apply ij.val.1
  have hj : Continuous (fun y : Y => y ij.val.2) := continuous_apply ij.val.2
  exact continuous_nnnorm.measurable.comp (Real.continuous_exp.comp (hj.sub hi)).measurable

private theorem conjugate_entry (y : Y) (u : N) (ij : UpperEntryPair (q + 1)) :
    upperEntryCoordinates (q + 1) (conjTorus (-y) u) ij =
      rootRatio y ij * upperEntryCoordinates (q + 1) u ij := by
  simp only [Langlands.GeneralLinear.upperEntryCoordinates_apply]
  change (torus (-y) * (u : G) * torus (-(-y))).val ij.val.1 ij.val.2 = _
  simp only [neg_neg, Units.val_mul, torus_val, Matrix.mul_diagonal, Matrix.diagonal_mul,
    rootRatio, sub_eq_add_neg, Real.exp_add, Pi.neg_apply]
  ring

private theorem map_scaleEntries (μ : AdditiveHaarMeasure ℝ) (y : Y) :
    (upperEntryProductMeasure μ (q + 1)).map (fun x : X => fun ij => rootRatio y ij * x ij) =
      tailModulus y • upperEntryProductMeasure μ (q + 1) := by
  let : μ.measure.IsAddHaarMeasure := μ.isAddHaar
  let : SigmaFinite μ.measure := inferInstance
  let f := fun x : X => fun ij => rootRatio y ij * x ij
  have hmap (ij : UpperEntryPair (q + 1)) := realHaar_map_mul μ.measure (rootRatio y ij) (rootRatio_ne_zero y ij)
  let ν := Measure.pi fun _ : UpperEntryPair (q + 1) => μ.measure
  change ν.map f = tailModulus y • ν
  have hs : ∀ ij : UpperEntryPair (q + 1), SigmaFinite
      (μ.measure.map (fun z => rootRatio y ij * z)) := by
    intro ij
    rw [hmap ij]
    infer_instance
  have he : ν.map f = Measure.pi (fun ij : UpperEntryPair (q + 1) =>
      ((‖rootRatio y ij‖₊)⁻¹ : ℝ≥0) • μ.measure) := by
    rw [show ν.map f = Measure.pi (fun ij : UpperEntryPair (q + 1) =>
        μ.measure.map (fun z => rootRatio y ij * z)) from
      Measure.pi_map_pi (μ := fun _ : UpperEntryPair (q + 1) => μ.measure)
        (f := fun ij z => rootRatio y ij * z) (hμ := hs)
        (fun ij => (measurable_const.mul measurable_id).aemeasurable)]
    simp_rw [hmap]
  rw [he]
  exact pi_nnreal_smul (fun _ : UpperEntryPair (q + 1) => μ.measure)
    (fun ij => (‖rootRatio y ij‖₊)⁻¹)

private theorem map_tailConjugation (μ : AdditiveHaarMeasure ℝ) (y : Y) :
    (entryHaar μ (q + 1)).map (conjTorus (-y)) = tailModulus y • entryHaar μ (q + 1) := by
  let e := upperEntryCoordinates (K := ℝ) (q + 1)
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
  rw [Measure.map_map (RealIwasawa.continuous_conjTorus_right (-y)).measurable e.symm.measurable, hEq,
    ← Measure.map_map e.symm.measurable hScale, map_scaleEntries,
    Measure.map_smul _ e.symm.measurable.aemeasurable]

private def shear (p : Y × N) : Y × N := (p.1, conjTorus (-p.1) p.2)

private theorem measurable_shear : Measurable (shear (q := q)) := by
  apply measurable_fst.prodMk
  apply Continuous.measurable
  apply Continuous.subtype_mk
  change Continuous (fun p : Y × N => torus (-p.1) * (p.2 : G) * torus (-(-p.1)))
  have ht : Continuous (fun p : Y × N => torus (-p.1)) := continuous_torus.comp continuous_fst.neg
  have ht' : Continuous (fun p : Y × N => torus (-(-p.1))) :=
    continuous_torus.comp continuous_fst.neg.neg
  exact (ht.mul (continuous_subtype_val.comp continuous_snd)).mul ht'

/-- The logarithmic diagonal measure with the triangular tail modulus. -/
def tailDiagonalMeasure (q : ℕ) : Measure (Fin (q + 1) → ℝ) :=
  volume.withDensity (fun y => (tailModulus y : ℝ≥0∞))

instance (q : ℕ) : SigmaFinite (tailDiagonalMeasure q) :=
  SigmaFinite.withDensity tailModulus

private theorem measurePreserving_shear (μ : AdditiveHaarMeasure ℝ) :
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
  rw [← lintegral_map hy (RealIwasawa.continuous_conjTorus_right (-y)).measurable,
    show ν.map (conjTorus (-y)) = tailModulus y • ν from map_tailConjugation μ y, lintegral_smul_measure]
  rfl

/-- The tail block factorization in compact, positive diagonal, upper unipotent order. -/
def tailChart (p : Coords) : G := p.2.val * torus p.1.1 * p.1.2.val

theorem continuous_tailChart : Continuous (tailChart (q := q)) :=
  ((continuous_subtype_val.comp continuous_snd).mul
    (continuous_torus.comp (continuous_fst.comp continuous_fst))).mul
      (continuous_subtype_val.comp (continuous_snd.comp continuous_fst))

/-- The triangular tail chart expresses any real group Haar measure as the product of the
logarithmic diagonal measure, entry-product Haar and compact Haar up to one constant. -/
def RealGapTailIwasawaStatement : Prop :=
  ∀ (q : ℕ) (μ : AdditiveHaarMeasure ℝ) (Haar : Measure (Langlands.GeneralLinear (q + 1) ℝ))
    (κ : Measure (unitaryCompact ℝ (q + 1))),
    Haar.IsHaarMeasure → κ.IsHaarMeasure → ∃ c : ℝ≥0, 0 < c ∧
    Haar = c • (((tailDiagonalMeasure q).prod (entryHaar μ (q + 1))).prod κ).map tailChart

set_option maxHeartbeats 800000 in
private theorem tailIwasawa (μ : AdditiveHaarMeasure ℝ) (Haar : Measure G) (hH : Haar.IsHaarMeasure)
    (κ : Measure Compact) (hκ : κ.IsHaarMeasure) :
    ∃ c : ℝ≥0, 0 < c ∧ Haar = c •
      (((tailDiagonalMeasure q).prod (entryHaar μ (q + 1))).prod κ).map tailChart := by
  let : κ.IsHaarMeasure := hκ
  let : Haar.IsHaarMeasure := hH
  let : Haar.IsMulRightInvariant := (RealGodement.realMatrixHaar_symmetries Haar).1
  obtain ⟨c, hc, hRight⟩ := exists_rightIwasawa_entryMeasure Haar κ
  let e := (upperEntryCoordinates (K := ℝ) (q + 1)).symm
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
  let entryChart (p : (Y × X) × Compact) : G := p.2.val * (e p.1.2).val * torus p.1.1
  have hEntryChart : Measurable entryChart :=
    (((continuous_subtype_val.comp continuous_snd).mul
      (continuous_subtype_val.comp (e.continuous.comp (continuous_snd.comp continuous_fst)))).mul
      (continuous_torus.comp (continuous_fst.comp continuous_fst))).measurable
  let fromEntries := Prod.map (Prod.map (id : Y → Y) e) (id : Compact → Compact)
  have hFromEntries : MeasurePreserving fromEntries source ((volume.prod ν).prod κ) :=
    ((MeasurePreserving.id _).prod (show MeasurePreserving e ξ ν from ⟨e.measurable, rfl⟩)).prod
      (MeasurePreserving.id _)
  let S := Prod.map (shear (q := q)) (id : Compact → Compact)
  have hChange : MeasurePreserving (S ∘ fromEntries) source (((tailDiagonalMeasure q).prod ν).prod κ) :=
    ((measurePreserving_shear μ).prod (MeasurePreserving.id κ)).comp hFromEntries
  have hChart : entryChart = tailChart ∘ (S ∘ fromEntries) := by
    funext p
    change p.2.val * (e p.1.2).val * torus p.1.1 =
      p.2.val * torus p.1.1 * (torus (-p.1.1) * (e p.1.2 : G) * torus (-(-p.1.1)))
    simp only [neg_neg, torus_neg, mul_assoc, mul_inv_cancel_left]
  change Haar = c • (((volume : Measure Y).prod (volume : Measure X)).prod κ).map entryChart at hRight
  refine ⟨c * b, mul_pos hc hb, ?_⟩
  change Haar = (c * b) • (((tailDiagonalMeasure q).prod ν).prod κ).map tailChart
  rw [hRight, hVol, Measure.prod_smul_right, Measure.prod_smul_left,
    Measure.map_smul _ hEntryChart.aemeasurable, smul_smul, hChart,
    ← Measure.map_map continuous_tailChart.measurable hChange.measurable, hChange.map_eq]

theorem realGapTailIwasawa : RealGapTailIwasawaStatement :=
  fun _ μ Haar κ hH hκ => tailIwasawa μ Haar hH κ hκ

end Langlands.Global.RankinSelbergGlobal.RealGapTailIwasawa
