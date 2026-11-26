import Langlands.Global.RankinSelberg.RealLocalIwasawaHaar
import Langlands.Global.RankinSelberg.RealIwasawaMeasure
import Langlands.Global.RankinSelberg.ArchimedeanIntegrals
import Langlands.Analysis.Local.QuotientNormalizingFunction
import Langlands.Analysis.Local.QuotientCompactOpenOrbitProof
import Langlands.HarmonicAnalysis.FiniteProductMeasureScaling

/-! # Explicit real Iwasawa measure on the unipotent quotient -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Matrix Set
open scoped ENNReal NNReal Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1050000

namespace Langlands.Global.RankinSelbergGlobal.RealIwasawaQuotientHaar

open Langlands.Archimedean (unitaryCompact)
open Langlands.GeneralLinear (UpperEntryPair upperEntryCoordinates upperEntryCoordinates_apply
  upperEntryProductMeasure upperEntryProductMeasure_isHaar)
open Langlands.QuotientIntegration (leftQuotientMap leftQuotientMap_subgroup_mul
  leftQuotient_isOpenQuotientMap IsNormalizingFunction)
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open Langlands.HarmonicAnalysis (pi_nnreal_smul)
open Langlands.LocalFactor.Archimedean (realStandardMeasure)
open ArchimedeanLocal RealIwasawa
open RealLocalIwasawaHaar (realIwasawaHaar)

private local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear n ℝ) := ⟨rfl⟩
private local instance (n : ℕ) : SecondCountableTopology (Langlands.GeneralLinear n ℝ) :=
  Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology
private local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear.upperUnipotent n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear.upperUnipotent n ℝ) := ⟨rfl⟩
private local instance (n : ℕ) : SecondCountableTopology (Langlands.GeneralLinear.upperUnipotent n ℝ) :=
  (upperEntryCoordinates (K := ℝ) n).isEmbedding.secondCountableTopology
private local instance (n : ℕ) : SecondCountableTopology (unitaryCompact ℝ n) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
private local instance (n : ℕ) : MeasurableSpace (unitaryCompact ℝ n) := borel _
private local instance (n : ℕ) : BorelSpace (unitaryCompact ℝ n) := ⟨rfl⟩
private local instance (r : ℕ) : MeasurableSpace (LeftUnipotentQuotient r ℝ) := borel _
private local instance (r : ℕ) : BorelSpace (LeftUnipotentQuotient r ℝ) := ⟨rfl⟩

variable {n : ℕ}
local notation "G" => Langlands.GeneralLinear n ℝ
local notation "N" => Langlands.GeneralLinear.upperUnipotent n ℝ
local notation "Cpt" => unitaryCompact ℝ n
local notation "Y" => Fin n → ℝ
local notation "X" => UpperEntryPair n → ℝ

/-- Inverse modulus of the action of the positive diagonal on the upper unipotent. -/
def rootModulus (y : Y) : ℝ≥0 :=
  ∏ ij : UpperEntryPair n, (Real.exp (y ij.1.2 - y ij.1.1)).toNNReal

theorem rootModulus_pos (y : Y) : 0 < rootModulus y :=
  Finset.prod_pos fun _ _ => Real.toNNReal_pos.mpr (Real.exp_pos _)

theorem measurable_rootModulus : Measurable (fun y : Y => (rootModulus y : ℝ≥0∞)) := by
  apply Measurable.coe_nnreal_ennreal
  unfold rootModulus
  exact Finset.measurable_prod _ fun p _ =>
    (continuous_real_toNNReal.comp (Real.continuous_exp.comp
      ((continuous_apply p.1.2).sub (continuous_apply p.1.1)))).measurable

/-- The logarithmic positive diagonal measure for the left unipotent quotient. -/
def logDiagonalMeasure (n : ℕ) : Measure (Fin n → ℝ) :=
  volume.withDensity (fun y => (rootModulus y : ℝ≥0∞))

instance logDiagonalMeasure_sigmaFinite (n : ℕ) : SigmaFinite (logDiagonalMeasure n) :=
  SigmaFinite.withDensity rootModulus

private theorem entry_conjTorus (y : Y) (u : N) (ij : UpperEntryPair n) :
    upperEntryCoordinates n (conjTorus y u) ij =
      Real.exp (y ij.1.1 - y ij.1.2) * upperEntryCoordinates n u ij := by
  simp only [upperEntryCoordinates_apply]
  change (torus y * u.val * torus (-y)).val ij.1.1 ij.1.2 = _
  rw [Units.val_mul, Units.val_mul, torus_val, torus_val, Matrix.mul_diagonal, Matrix.diagonal_mul, Pi.neg_apply,
    sub_eq_add_neg, Real.exp_add]
  ring

private def scaleEntries (y : Y) (x : X) : X := fun ij => Real.exp (y ij.1.1 - y ij.1.2) * x ij

private theorem measurable_scaleEntries (y : Y) : Measurable (scaleEntries y) :=
  Measurable.of_eval fun ij => measurable_const.mul (measurable_pi_apply ij)

private theorem map_scaleEntries (y : Y) :
    (volume : Measure X).map (scaleEntries y) = rootModulus y • volume := by
  let c (ij : UpperEntryPair n) := Real.exp (y ij.1.1 - y ij.1.2)
  let b (ij : UpperEntryPair n) := (Real.exp (y ij.1.2 - y ij.1.1)).toNNReal
  have hb (ij : UpperEntryPair n) : (volume : Measure ℝ).map (fun v => c ij * v) = b ij • volume := by
    have hp : 0 < c ij := Real.exp_pos _
    rw [Real.map_volume_mul_left hp.ne', abs_of_pos (inv_pos.mpr hp)]
    dsimp only [b, c]
    rw [← Real.exp_neg, neg_sub]
    rfl
  have hs (ij : UpperEntryPair n) : SigmaFinite ((volume : Measure ℝ).map (fun v => c ij * v)) := by
    rw [hb]
    infer_instance
  change (Measure.pi fun _ : UpperEntryPair n => (volume : Measure ℝ)).map (fun x i => c i * x i) = _
  rw [Measure.pi_map_pi (hμ := hs) (fun _ => (measurable_const.mul measurable_id).aemeasurable)]
  simp_rw [hb]
  exact pi_nnreal_smul (fun _ => (volume : Measure ℝ)) b

private theorem map_conjTorus (ν : Measure N) [ν.IsHaarMeasure] (y : Y) :
    ν.map (conjTorus y) = rootModulus y • ν := by
  let e := upperEntryCoordinates (K := ℝ) n
  let η : Measure N := (volume : Measure X).map e.symm
  let : η.IsHaarMeasure := by
    let : SigmaFinite realStandardMeasure.measure := inferInstanceAs (SigmaFinite (volume : Measure ℝ))
    exact upperEntryProductMeasure_isHaar (d := n) realStandardMeasure
  have hEq := Measure.isMulLeftInvariant_eq_smul ν η
  rw [hEq, Measure.map_smul _ (continuous_conjTorus_right y).measurable.aemeasurable]
  have hcomm : conjTorus y ∘ e.symm = e.symm ∘ scaleEntries y := by
    funext x
    apply e.injective
    rw [Function.comp_apply, Function.comp_apply, e.apply_symm_apply]
    funext i
    change upperEntryCoordinates n (conjTorus y (e.symm x)) i = _
    rw [entry_conjTorus]
    change _ * e (e.symm x) i = _
    rw [e.apply_symm_apply]
    rfl
  have hm : η.map (conjTorus y) = rootModulus y • η := by
    change ((volume : Measure X).map e.symm).map _ = _
    rw [Measure.map_map (continuous_conjTorus_right y).measurable e.symm.measurable, hcomm,
      ← Measure.map_map e.symm.measurable (measurable_scaleEntries y), map_scaleEntries,
      Measure.map_smul _ e.symm.measurable.aemeasurable]
  rw [hm, smul_comm]

private def shear (p : Y × N) : Y × N := (p.1, conjTorus p.1 p.2)

private theorem measurable_shear : Measurable (shear (n := n)) := by
  apply measurable_fst.prodMk
  apply Continuous.measurable
  apply Continuous.subtype_mk
  change Continuous (fun p : Y × N => torus p.1 * p.2.val * torus (-p.1))
  exact (((continuous_torus.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd))).mul
    (continuous_torus.comp continuous_fst.neg)

private theorem measurePreserving_shear (ν : Measure N) [ν.IsHaarMeasure] [SigmaFinite ν] :
    MeasurePreserving (shear (n := n)) (volume.prod ν) ((logDiagonalMeasure n).prod ν) := by
  refine ⟨measurable_shear, Measure.ext_of_lintegral _ fun F hF => ?_⟩
  rw [lintegral_map hF measurable_shear]
  change (∫⁻ p, (F ∘ shear) p ∂volume.prod ν) = ∫⁻ p, F p ∂(logDiagonalMeasure n).prod ν
  rw [lintegral_prod _ (hF.comp measurable_shear).aemeasurable, lintegral_prod _ hF.aemeasurable,
    logDiagonalMeasure,
    lintegral_withDensity_eq_lintegral_mul _ measurable_rootModulus hF.lintegral_prod_right']
  apply lintegral_congr
  intro y
  change (∫⁻ z, F (y, conjTorus y z) ∂ν) = (rootModulus y : ℝ≥0∞) * ∫⁻ z, F (y, z) ∂ν
  have hy : Measurable (fun z : N => F (y, z)) := hF.comp (measurable_const.prodMk measurable_id)
  rw [← lintegral_map hy (continuous_conjTorus_right y).measurable,
    map_conjTorus ν y, lintegral_smul_measure]
  rfl

private def unipotentFirstChart (p : (Y × N) × Cpt) : G := p.1.2.val * torus p.1.1 * p.2.val

private theorem continuous_unipotentFirstChart : Continuous (unipotentFirstChart (n := n)) :=
  ((continuous_subtype_val.comp (continuous_snd.comp continuous_fst)).mul
    (continuous_torus.comp (continuous_fst.comp continuous_fst))).mul
    (continuous_subtype_val.comp continuous_snd)

private def GroupHaarChartWith (mN : MeasurableSpace N) (mK : MeasurableSpace Cpt) : Prop :=
  letI := mN
  letI := mK
  ∀ (μ : Measure G) (ν : Measure N) (κ : Measure Cpt),
    μ.IsHaarMeasure → ν.IsHaarMeasure → κ.IsHaarMeasure →
    ∃ C : ℝ≥0, 0 < C ∧ μ = C • ((volume.prod ν).prod κ).map
      (fun p : (Y × N) × Cpt => torus p.1.1 * p.1.2.val * p.2.val)

private theorem groupHaar_chart (μ : Measure G) (ν : Measure N) (κ : Measure Cpt)
    (hμ : μ.IsHaarMeasure) (hν : ν.IsHaarMeasure) (hκ : κ.IsHaarMeasure) :
    ∃ C : ℝ≥0, 0 < C ∧ μ = C • (((logDiagonalMeasure n).prod ν).prod κ).map unipotentFirstChart := by
  let : ν.IsHaarMeasure := hν
  let : SigmaFinite ν := inferInstance
  have hN : borel N = (borel G).comap (Subtype.val : N → G) := borel_comap
  have hK : borel Cpt = (borel G).comap (Subtype.val : Cpt → G) := borel_comap
  have hChart : GroupHaarChartWith (n := n) ((borel G).comap (Subtype.val : N → G))
      ((borel G).comap (Subtype.val : Cpt → G)) := realIwasawaHaar n
  rw [← hN, ← hK] at hChart
  obtain ⟨C, hC, h⟩ := hChart μ ν κ hμ hν hκ
  refine ⟨C, hC, ?_⟩
  have he : (fun p : (Y × N) × Cpt => torus p.1.1 * p.1.2.val * p.2.val) =
      unipotentFirstChart ∘ Prod.map shear id := by
    funext p
    change torus p.1.1 * p.1.2.val * p.2.val =
      (torus p.1.1 * p.1.2.val * torus (-p.1.1)) * torus p.1.1 * p.2.val
    rw [torus_neg, inv_mul_cancel_right]
  rw [h, he, ← Measure.map_map continuous_unipotentFirstChart.measurable (measurable_shear.prodMap measurable_id),
    ((measurePreserving_shear ν).prod (MeasurePreserving.id κ)).map_eq]

/-- The quotient point represented by a positive diagonal times an orthogonal matrix. -/
def quotientChart {r : ℕ} (p : (Fin (r + 1) → ℝ) × unitaryCompact ℝ (r + 1)) : LeftUnipotentQuotient r ℝ :=
  leftQuotientMap (Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ) (torus p.1 * p.2.val)

/-- The diagonal and compact coordinates give a continuous map into the quotient. -/
theorem continuous_quotientChart {r : ℕ} : Continuous (quotientChart (r := r)) :=
  (leftQuotient_isOpenQuotientMap _).continuous.comp
    ((continuous_torus.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd))

theorem measurable_quotientChart {r : ℕ} : Measurable (quotientChart (r := r)) :=
  continuous_quotientChart.measurable

/-- Any compatible real quotient Haar measure is a positive multiple of the
explicit product of the logarithmic diagonal and compact Haar measures. -/
def RealIwasawaQuotientHaarStatement : Prop :=
  ∀ (r : ℕ) (D : RealQuotientMeasureData r) (κ : Measure (unitaryCompact ℝ (r + 1))),
    κ.IsHaarMeasure → ∃ C : ℝ≥0, 0 < C ∧
      D.measure = C • ((logDiagonalMeasure (r + 1)).prod κ).map quotientChart

theorem realIwasawaQuotientHaar : RealIwasawaQuotientHaarStatement := by
  intro r D κ hκ
  let H := Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ
  let ν := D.unipotentHaar
  let : κ.IsHaarMeasure := hκ
  let : D.groupHaar.IsHaarMeasure := D.groupHaar_isHaar
  let : ν.IsHaarMeasure := D.unipotentHaar_isHaar
  let : ν.IsMulRightInvariant := D.unipotentHaar_rightInvariant
  let : SigmaFinite ν := inferInstance
  let : SigmaFinite κ := inferInstance
  obtain ⟨β, hβ, hβsupp, hβ0, hβ1⟩ := exists_unipotent_bump (n := r + 1)
  let mβ := ∫ u, β u ∂ν
  have hmβ : 0 < mβ := hβ.integral_pos_of_hasCompactSupport_nonneg_nonzero hβsupp hβ0
    (x := 1) (by rw [hβ1]; exact one_ne_zero)
  let B (u : H) := (ENNReal.ofReal mβ)⁻¹ * ENNReal.ofReal (β u)
  have hB : Measurable B := (hβ.measurable.ennreal_ofReal).const_mul _
  have hIntB : ∫⁻ u, B u ∂ν = 1 := by
    simp only [B, lintegral_const_mul _ hβ.measurable.ennreal_ofReal,
      ← ofReal_integral_eq_lintegral_ofReal (hβ.integrable_of_hasCompactSupport hβsupp) (ae_of_all _ hβ0)]
    exact ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr hmβ) ENNReal.ofReal_ne_top
  let ρ (g : Langlands.GeneralLinear (r + 1) ℝ) := B (npart g)
  have hρ : IsNormalizingFunction H ν ρ := by
    refine ⟨hB.comp continuous_npart.measurable, fun g => ?_⟩
    simp_rw [ρ, npart_unipotent_mul]
    rw [lintegral_mul_right_eq_self]
    exact hIntB
  obtain ⟨C, hC, hG⟩ := groupHaar_chart D.groupHaar ν κ D.groupHaar_isHaar D.unipotentHaar_isHaar hκ
  refine ⟨C, hC, Measure.ext_of_lintegral _ fun F hF => ?_⟩
  let dy := logDiagonalMeasure (r + 1)
  let τ := leftQuotientMap H
  have hτ : Measurable τ := (leftQuotient_isOpenQuotientMap H).continuous.measurable
  have hFun : Measurable (fun g => F (τ g) * ρ g) := (hF.comp hτ).mul hρ.measurable
  rw [D.compatible.lintegral_eq_lintegral_mul_comp isClosed_upperUnipotent hρ hF,
    hG, lintegral_smul_measure, lintegral_map hFun continuous_unipotentFirstChart.measurable,
    lintegral_smul_measure, lintegral_map hF measurable_quotientChart]
  congr 1
  let U := fun p : (((Fin (r + 1) → ℝ) × H) × unitaryCompact ℝ (r + 1)) =>
    F (quotientChart (p.1.1, p.2)) * B p.1.2
  have hEval (p : ((Fin (r + 1) → ℝ) × H) × unitaryCompact ℝ (r + 1)) :
      F (τ (unipotentFirstChart p)) * ρ (unipotentFirstChart p) = U p := by
    have hpt : τ (unipotentFirstChart p) = quotientChart (p.1.1, p.2) := by
      change leftQuotientMap H (p.1.2.val * torus p.1.1 * p.2.val) =
        leftQuotientMap H (torus p.1.1 * p.2.val)
      rw [mul_assoc, leftQuotientMap_subgroup_mul]
    rw [hpt]
    change _ * B (npart (p.1.2.val * torus p.1.1 * p.2.val)) = _
    rw [npart_iwasawa]
  simp_rw [hEval]
  have hU : Measurable U := (hF.comp (measurable_quotientChart.comp
    ((measurable_fst.comp measurable_fst).prodMk measurable_snd))).mul
      (hB.comp (measurable_snd.comp measurable_fst))
  change (∫⁻ p, U p ∂(dy.prod ν).prod κ) = ∫⁻ p, (F ∘ quotientChart) p ∂dy.prod κ
  rw [lintegral_prod_symm _ hU.aemeasurable,
    lintegral_prod_symm _ (hF.comp measurable_quotientChart).aemeasurable]
  apply lintegral_congr
  intro k
  have hUk : Measurable (fun p => U (p, k)) := hU.comp (measurable_id.prodMk measurable_const)
  rw [lintegral_prod _ hUk.aemeasurable]
  congr 1
  funext y
  change (∫⁻ u, F (quotientChart (y, k)) * B u ∂ν) = F (quotientChart (y, k))
  rw [lintegral_const_mul _ hB, hIntB, mul_one]

end Langlands.Global.RankinSelbergGlobal.RealIwasawaQuotientHaar
