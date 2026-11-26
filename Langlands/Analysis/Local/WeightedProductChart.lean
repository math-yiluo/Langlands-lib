import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.Constructions.SumProd

/-! # Restricted weighted measures in product coordinates -/

noncomputable section

namespace Langlands.Analysis

open MeasureTheory MeasureTheory.Measure Set _root_.Topology
open scoped NNReal ENNReal

/-- An injective Borel coordinate restricts a transported measure to the
image of a measurable set. -/
theorem map_restrict_image_of_embedding {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {e : X → Y} (he : MeasurableEmbedding e) (μ : Measure X) (D : Set X) :
    (μ.restrict D).map e = (μ.map e).restrict (e '' D) := by
  rw [he.restrict_map, preimage_image_eq _ he.injective]

/-- Restriction to a smaller set keeps an affine chart's Haar scale. -/
theorem map_restrict_subset_of_eq {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {e : X → Y} (he : MeasurableEmbedding e) (μ : Measure X) (ξ : Measure Y)
    {D₀ D : Set X} (hD : MeasurableSet D) (hsub : D ⊆ D₀) {c : ℝ≥0}
    (hμ : (μ.restrict D₀).map e = c • ξ.restrict (e '' D₀)) :
    (μ.restrict D).map e = c • ξ.restrict (e '' D) := by
  have h := map_restrict_image_of_embedding he (μ.restrict D₀) D
  rw [Measure.restrict_restrict hD, inter_eq_self_of_subset_left hsub, hμ,
    Measure.restrict_smul, Measure.restrict_restrict (he.measurableSet_image.2 hD),
    inter_eq_self_of_subset_left (image_mono hsub)] at h
  exact h

/-- A compact measurable patch has finite measure in the subtype. -/
theorem isFiniteMeasure_comap_subtype_of_isCompact {X : Type*}
    [TopologicalSpace X] [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
    {D : Set X} (hD : MeasurableSet D) (hc : IsCompact D) :
    IsFiniteMeasure (μ.comap (Subtype.val : D → X)) := by
  refine ⟨?_⟩
  rw [(MeasurableEmbedding.subtype_coe hD).comap_apply, image_univ, Subtype.range_coe]
  exact hc.measure_lt_top

/-- A map defined on the chart image can be pushed forward using the
coordinate measure, when it is measurable in the coordinates. -/
theorem map_map_of_measurableEmbedding {X Y Z : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    {e : X → Y} (he : MeasurableEmbedding e) (μ : Measure X) (f : Y → Z)
    (hf : Measurable (f ∘ e)) : (μ.map e).map f = μ.map (f ∘ e) :=
  (he.aemeasurable_map_iff.mpr hf.aemeasurable).map_map_of_aemeasurable he.measurable.aemeasurable

section Product

variable {S W Q A : Type*} [TopologicalSpace S] [TopologicalSpace W]
  [TopologicalSpace Q] [TopologicalSpace A]
  [MeasurableSpace S] [MeasurableSpace W] [MeasurableSpace Q] [MeasurableSpace A]

/-- Measurable open product coordinates pull back a restricted product with
constant density to the product coordinate measure with that density. -/
theorem weightedProductChart {BS : Set S} {BW : Set W} (hBS : MeasurableSet BS)
    (hBW : MeasurableSet BW) (ξS : Measure S) [SFinite ξS]
    (ξW : Measure W) [SFinite ξW] (ν : Measure Q) [SFinite ν] (τ : Measure A) [SFinite τ]
    [SFinite (ξS.comap (Subtype.val : BS → S))] [SFinite (ξW.comap (Subtype.val : BW → W))]
    {c : BW → Q} {t : BS → A} (hc : IsOpenEmbedding c) (ht : IsOpenEmbedding t)
    (hcm : Measurable c) (htm : Measurable t)
    (dQ dT : ℝ≥0)
    (hQc : (dQ • ξW.comap Subtype.val).map c = ν.restrict (range c))
    (hTc : (dT • ξS.comap Subtype.val).map t = τ.restrict (range t))
    (w : A → ℝ≥0) (w₀ : ℝ≥0) (hw : ∀ x, w (t x) = w₀)
    (hV : MeasurableSet (range c ×ˢ range t)) :
    let B := BS ×ˢ BW
    let z := fun x : B => (c ⟨x.val.2, x.property.2⟩, t ⟨x.val.1, x.property.1⟩)
    let V := range c ×ˢ range t
    IsOpenEmbedding z ∧ range z = V ∧
      ((w₀ * (dT * dQ)) • (ξS.prod ξW).comap Subtype.val).map z =
        ((ν.prod τ).withDensity fun p => (w p.2 : ℝ≥0∞)).restrict V := by
  let B := BS ×ˢ BW
  let z := fun x : B => (c ⟨x.val.2, x.property.2⟩, t ⟨x.val.1, x.property.1⟩)
  let V := range c ×ˢ range t
  let e := Homeomorph.Set.prod BS BW
  let v : BW × BS → Q × A := Prod.map c t
  have hz : z = v ∘ Prod.swap ∘ e := rfl
  have hzE : IsOpenEmbedding z := by
    rw [hz]
    exact (hc.prodMap ht).comp ((Homeomorph.prodComm BS BW).isOpenEmbedding.comp e.isOpenEmbedding)
  have hzr : range z = V := by
    rw [hz, range_comp, range_comp, e.surjective.range_eq, image_univ, Prod.swap_surjective.range_eq,
      image_univ]
    exact Set.range_prodMap
  let mS := ξS.comap (Subtype.val : BS → S)
  let mW := ξW.comap (Subtype.val : BW → W)
  have hBe : MeasurableEmbedding (Subtype.val : B → S × W) := .subtype_coe (hBS.prod hBW)
  have he : Measurable e :=
    (measurable_fst.comp measurable_subtype_coe).subtype_mk.prodMk
      (measurable_snd.comp measurable_subtype_coe).subtype_mk
  have he' : Measurable e.symm :=
    ((measurable_subtype_coe.comp measurable_fst).prodMk
      (measurable_subtype_coe.comp measurable_snd)).subtype_mk
  have hBmap : (mS.prod mW).map e.symm = (ξS.prod ξW).comap (Subtype.val : B → S × W) := by
    apply hBe.map_injective
    rw [hBe.map_comap, Subtype.range_coe, Measure.map_map hBe.measurable he']
    change (mS.prod mW).map (Prod.map Subtype.val Subtype.val) = _
    rw [← Measure.map_prod_map _ _ measurable_subtype_coe measurable_subtype_coe,
      show mS.map Subtype.val = ξS.restrict BS from map_comap_subtype_coe hBS ξS,
      show mW.map Subtype.val = ξW.restrict BW from map_comap_subtype_coe hBW ξW,
      Measure.prod_restrict]
  have hcomp : z ∘ e.symm = v ∘ Prod.swap := by
    rw [hz, Function.comp_assoc, Function.comp_assoc]
    exact congrArg (fun f => v ∘ Prod.swap ∘ f) (funext e.apply_symm_apply)
  have hv : Measurable v := (hcm.comp measurable_fst).prodMk (htm.comp measurable_snd)
  have hzm : Measurable z := (hv.comp measurable_swap).comp he
  have hρ : ((ν.prod τ).withDensity fun p => (w p.2 : ℝ≥0∞)).restrict V =
      w₀ • (ν.prod τ).restrict V := by
    rw [restrict_withDensity hV]
    have hw' : (fun p : Q × A => (w p.2 : ℝ≥0∞)) =ᵐ[(ν.prod τ).restrict V] fun _ => (w₀ : ℝ≥0∞) := by
      filter_upwards [ae_restrict_mem hV] with p hp
      obtain ⟨x, hx⟩ := hp.2
      rw [← hx, hw]
    rw [withDensity_congr_ae hw', withDensity_const]
    rfl
  refine ⟨hzE, hzr, ?_⟩
  rw [hρ, ← hBmap, Measure.map_smul _ hzm.aemeasurable, Measure.map_map hzm he',
    hcomp, ← Measure.map_map hv measurable_swap, Measure.prod_swap,
    ← Measure.map_prod_map _ _ hcm htm]
  change _ = w₀ • (ν.prod τ).restrict (range c ×ˢ range t)
  rw [← Measure.prod_restrict, ← hQc, ← hTc, Measure.map_smul _ hcm.aemeasurable,
    Measure.map_smul _ htm.aemeasurable, Measure.prod_smul_left, Measure.prod_smul_right,
    smul_smul, smul_smul, mul_assoc w₀ dQ dT, mul_comm dQ dT]

end Product

section Transport

variable {X Y G R : Type*}
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
  [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R]

/-- An exact coordinate pushforward gives the restricted pushforward on the
open branch, with ambient Haar transported through a preserving homeomorphism. -/
theorem localPushforward_of_affine_chart {B : Set X} (hB : MeasurableSet B)
    (η : Measure X) (ξ : Measure R) (μ : Measure G) (ρ : Measure Y)
    {z : B → Y} (hz : IsOpenEmbedding z) (p : Y → G)
    (m : G ≃ₜ G) (hμm : μ.map m = μ)
    {a : G → R} (ha : IsOpenEmbedding a)
    {K : Set G} (c d : ℝ≥0) (hK : (μ.restrict K).map a = c • ξ.restrict (a '' K))
    (ψ : X → R) (hψ : IsOpenEmbedding (ψ ∘ (Subtype.val : B → X)))
    (hcomp : a ∘ m ∘ p ∘ z = ψ ∘ (Subtype.val : B → X))
    (D : Set R) (hD : range (ψ ∘ (Subtype.val : B → X)) = D) (hDK : D ⊆ a '' K)
    (hψM : ((d • η.restrict B).map ψ) = c • ξ.restrict D)
    (hsrc : (d • η.comap (Subtype.val : B → X)).map z = ρ.restrict (range z)) :
    IsOpenEmbedding (fun y : range z => p y.val) ∧
      (ρ.restrict (range z)).map p = μ.restrict (p '' range z) := by
  let b : G → R := a ∘ m
  have hb : IsOpenEmbedding b := ha.comp m.isOpenEmbedding
  have hEq : b ∘ (p ∘ z) = ψ ∘ (Subtype.val : B → X) := hcomp
  have hp : IsOpenEmbedding (p ∘ z) :=
    IsOpenEmbedding.of_comp _ hb (hEq.symm ▸ hψ)
  constructor
  · let z' := hz.isEmbedding.toHomeomorph
    have heq : (fun y : range z => p y.val) = (p ∘ z) ∘ z'.symm := by
      funext y
      exact congrArg (fun x : range z => p x.val) (z'.apply_symm_apply y).symm
    rw [heq]
    exact hp.comp z'.symm.isOpenEmbedding
  have him : b '' (p '' range z) = D := by
    rw [← range_comp, ← range_comp, hEq, hD]
  have hpm : IsOpen (p '' range z) := by
    rw [← range_comp]
    exact hp.isOpen_range
  have hsub : m '' (p '' range z) ⊆ K := by
    rintro _ ⟨x, hx, rfl⟩
    have hh : a (m x) ∈ a '' K := hDK (him ▸ mem_image_of_mem b hx)
    obtain ⟨k, hk, hek⟩ := hh
    exact ha.injective hek ▸ hk
  have htarget : (μ.restrict (p '' range z)).map b = c • ξ.restrict D := by
    have h := map_restrict_subset_of_eq ha.measurableEmbedding μ ξ
      (m.isOpenMap _ hpm).measurableSet hsub hK
    have him' : a '' (m '' (p '' range z)) = D := by
      rw [image_image]
      exact him
    change (μ.restrict (p '' range z)).map (a ∘ m) = _
    rw [← Measure.map_map ha.continuous.measurable m.continuous.measurable,
      map_restrict_image_of_embedding m.measurableEmbedding, hμm, h, him']
  have hBe : MeasurableEmbedding (Subtype.val : B → X) := .subtype_coe hB
  have hψmap : (d • η.comap (Subtype.val : B → X)).map (ψ ∘ Subtype.val) =
      c • ξ.restrict D := by
    rw [← map_map_of_measurableEmbedding hBe _ ψ hψ.continuous.measurable,
      Measure.map_smul _ hBe.measurable.aemeasurable, map_comap_subtype_coe hB, hψM]
  apply hb.measurableEmbedding.map_injective
  rw [← hsrc, map_map_of_measurableEmbedding hz.measurableEmbedding _ _ hp.continuous.measurable,
    Measure.map_map hb.continuous.measurable hp.continuous.measurable, hEq, hψmap, htarget]

end Transport
end Langlands.Analysis
