import Langlands.Global.RankinSelberg.ComplexLocalIwasawaHaar
import Langlands.Group.GL.TriangularParabolic

/-! # Block parabolic and unitary coordinates for complex Haar measure -/

noncomputable section

open Set MeasureTheory MeasureTheory.Measure
open scoped Classical Matrix.Norms.Operator NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexParabolicHaar

open Langlands.GeneralLinear (BlockShape upperTriangularSubgroup mem_upperTriangularSubgroup_iff
  upperUnipotent_le_upperTriangular)
open Langlands.Archimedean (unitaryCompact)
open Langlands.Archimedean.ComplexDuality (isCompact_unitaryCompact)
open ComplexLocalIwasawa (exists_iwasawa)
open ComplexLocalWhittakerGauge (logTorus logTorus_val)

local notation "G" => fun n => Langlands.GeneralLinear n ℂ
local notation "K" => fun n => unitaryCompact ℂ n
local notation "P" => fun B => BlockShape.parabolic B ℂ
local notation "M" => fun B => BlockShape.Levi B ℂ
local notation "U" => fun B => BlockShape.unipotentRadical B ℂ

local instance parabolicHaarGLMeasurable (n : ℕ) : MeasurableSpace (G n) := borel _
local instance parabolicHaarGLBorel (n : ℕ) : BorelSpace (G n) := ⟨rfl⟩
local instance parabolicHaarGLSecondCountable (n : ℕ) : SecondCountableTopology (G n) :=
  Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology
local instance parabolicHaarGLLocallyCompact (n : ℕ) : LocallyCompactSpace (G n) :=
  Units.isOpenEmbedding_val.locallyCompactSpace

variable {n : ℕ} (B : BlockShape n)

private def leviRadicalHomeomorph : M B × U B ≃ₜ P B :=
  (((Homeomorph.inv (M B)).prodCongr (Homeomorph.inv (U B))).trans
    (Homeomorph.prodComm (M B) (U B))).trans ((B.decompositionHomeomorph ℂ).symm.trans (Homeomorph.inv (P B)))

private theorem leviRadicalHomeomorph_apply (x : M B × U B) :
    leviRadicalHomeomorph B x = B.leviInParabolic ℂ x.1 * x.2.val := by
  change ((x.2⁻¹ : U B).val * B.leviInParabolic ℂ x.1⁻¹)⁻¹ = _
  rw [mul_inv_rev, map_inv, inv_inv, Subgroup.coe_inv, inv_inv]

private def leftShift (q x : M B × U B) : M B × U B :=
  (q.1 * x.1, B.leviAction ℂ x.1⁻¹ q.2 * x.2)

private theorem leviRadical_leftShift (q x : M B × U B) :
    leviRadicalHomeomorph B (leftShift B q x) = leviRadicalHomeomorph B q * leviRadicalHomeomorph B x := by
  have hAct : (B.leviAction ℂ x.1⁻¹ q.2).val =
      B.leviInParabolic ℂ x.1⁻¹ * q.2.val * (B.leviInParabolic ℂ x.1⁻¹)⁻¹ := rfl
  simp only [leviRadicalHomeomorph_apply, leftShift, map_mul, Subgroup.coe_mul]
  rw [hAct, map_inv, inv_inv]
  group

private theorem continuous_leftShift_snd (q : M B × U B) :
    Continuous (fun x : M B × U B => (leftShift B q x).2) :=
  (((B.continuous_leviAction ℂ).comp (continuous_fst.inv.prodMk continuous_const)).mul continuous_snd)

private theorem parabolicHaar_isHaar (μM : Measure (M B)) (ν : Measure (U B))
    [μM.IsHaarMeasure] [ν.IsHaarMeasure] [SFinite μM] [SFinite ν] :
    ((μM.prod ν).map (leviRadicalHomeomorph B)).IsHaarMeasure := by
  let e := leviRadicalHomeomorph B
  let σ := (μM.prod ν).map e
  let : IsFiniteMeasureOnCompacts σ := IsFiniteMeasureOnCompacts.map _ e
  let : IsOpenPosMeasure σ := e.continuous.isOpenPosMeasure_map e.surjective
  refine { map_mul_left_eq_self := fun p => ?_ }
  let q := e.symm p
  have he : (p * ·) ∘ e = e ∘ leftShift B q := by
    funext x
    change p * e x = e (leftShift B q x)
    rw [leviRadical_leftShift B q x, e.apply_symm_apply]
  have hp : MeasurePreserving (leftShift B q) (μM.prod ν) (μM.prod ν) :=
    (measurePreserving_mul_left μM q.1).skew_product (continuous_leftShift_snd B q).measurable
      (Filter.Eventually.of_forall fun t => map_mul_left_eq_self ν (B.leviAction ℂ t⁻¹ q.2))
  change Measure.map (p * ·) σ = σ
  rw [show σ = (μM.prod ν).map e from rfl, Measure.map_map (measurable_const_mul _) e.measurable,
    he, ← Measure.map_map e.measurable hp.measurable, hp.map_eq]

/-- The multiplication map for Levi, radical, unitary coordinates. -/
def leviRadicalUnitary : (M B × U B) × K n → G n :=
  fun x => B.leviEmbedding ℂ x.1.1 * x.1.2.val.val * x.2.val

/-- The multiplication map for unitary, radical, Levi coordinates, using the same
product order for the coordinates. -/
def unitaryRadicalLevi : (M B × U B) × K n → G n :=
  fun x => x.2.val * x.1.2.val.val * B.leviEmbedding ℂ x.1.1

private theorem continuous_leviRadicalUnitary : Continuous (leviRadicalUnitary B) :=
  (((B.leviEmbeddingContinuous ℂ).continuous.comp (continuous_fst.comp continuous_fst)).mul
    (continuous_subtype_val.comp (continuous_subtype_val.comp (continuous_snd.comp continuous_fst)))).mul
      (continuous_subtype_val.comp continuous_snd)

private theorem continuous_unitaryRadicalLevi : Continuous (unitaryRadicalLevi B) :=
  ((continuous_subtype_val.comp continuous_snd).mul
    (continuous_subtype_val.comp (continuous_subtype_val.comp (continuous_snd.comp continuous_fst)))).mul
      ((B.leviEmbeddingContinuous ℂ).continuous.comp (continuous_fst.comp continuous_fst))

private theorem exists_parabolic_unitary (g : G n) :
    ∃ p ∈ P B, ∃ k ∈ K n, g = p * k := by
  obtain ⟨u, y, k, hg⟩ := exists_iwasawa g
  have hT : logTorus y ∈ upperTriangularSubgroup n ℂ := by
    apply (mem_upperTriangularSubgroup_iff _).mpr
    intro i j hij
    change (logTorus y).val i j = 0
    rw [logTorus_val, Matrix.diagonal_apply_ne _ hij.ne']
  exact ⟨u.val * logTorus y, B.upperTriangularSubgroup_le_parabolic ℂ
    (mul_mem (upperUnipotent_le_upperTriangular n ℂ u.2) hT), k.val, k.2, hg⟩

/-- Haar measure of the actual complex general linear group admits Levi, radical,
unitary product coordinates. Inversion preserves the constant and gives unitary,
radical, Levi coordinates when the supplied factor measures are inversion invariant. -/
def ComplexParabolicHaarStatement : Prop :=
  ∀ (n : ℕ) (B : BlockShape n) (μ : Measure (G n)) (μM : Measure (M B))
    (ν : Measure (U B)) (κ : Measure (K n)), μ.IsHaarMeasure → μM.IsHaarMeasure →
      ν.IsHaarMeasure → κ.IsHaarMeasure → ∃ c : ℝ≥0, 0 < c ∧
    μ = c • Measure.map (leviRadicalUnitary B) ((μM.prod ν).prod κ) ∧
    (μ.IsInvInvariant → μM.IsInvInvariant → ν.IsInvInvariant → κ.IsInvInvariant →
      μ = c • Measure.map (unitaryRadicalLevi B) ((μM.prod ν).prod κ))

set_option maxHeartbeats 1000000 in
theorem complexParabolicHaar : ComplexParabolicHaarStatement := by
  intro n B μ μM ν κ hμ hμM hν hκ
  let : μ.IsHaarMeasure := hμ
  let : μM.IsHaarMeasure := hμM
  let : ν.IsHaarMeasure := hν
  let : κ.IsHaarMeasure := hκ
  let : LocallyCompactSpace (U B) := B.unipotentRadicalLocallyCompactSpace ℂ
  let : LocallyCompactSpace (M B) := inferInstanceAs
    (LocallyCompactSpace (∀ i : Fin B.length, G (B.size i)))
  let : SecondCountableTopology (P B) := inferInstanceAs
    (SecondCountableTopology (B.parabolic ℂ : Set (G n)))
  let : SecondCountableTopology (U B) := inferInstanceAs
    (SecondCountableTopology (B.unipotentRadical ℂ : Set (B.parabolic ℂ)))
  let : SecondCountableTopology (M B) := inferInstance
  let : SigmaFinite μM := inferInstance
  let : SigmaFinite ν := inferInstance
  let e := leviRadicalHomeomorph B
  let σ := (μM.prod ν).map e
  let : σ.IsHaarMeasure := parabolicHaar_isHaar B μM ν
  obtain ⟨c, hc, hμc⟩ := Langlands.CompactFactorization.exists_pos_eq_smul_map_mul_prod
    μ (P B) (B.isClosed_parabolic ℂ) (K n) (isCompact_unitaryCompact n)
    (exists_parabolic_unitary B) σ κ
  have hLeft : μ = c • Measure.map (leviRadicalUnitary B) ((μM.prod ν).prod κ) := by
    rw [hμc]
    have hProd : σ.prod κ = Measure.map (Prod.map e id) ((μM.prod ν).prod κ) := by
      rw [← Measure.map_prod_map _ _ e.measurable measurable_id, Measure.map_id]
    have hm : Measurable (fun p : P B × K n => p.1.val * p.2.val) :=
      (measurable_subtype_coe.comp measurable_fst).mul (measurable_subtype_coe.comp measurable_snd)
    have he : (fun p : P B × K n => p.1.val * p.2.val) ∘ Prod.map e id = leviRadicalUnitary B := by
      funext p
      exact congrArg (fun q : P B => q.val * p.2.val) (leviRadicalHomeomorph_apply B p.1)
    rw [hProd, Measure.map_map hm (e.measurable.prodMap measurable_id), he]
  refine ⟨c, hc, hLeft, ?_⟩
  intro hμi hμMi hνi hκi
  let : μ.IsInvInvariant := hμi
  let : μM.IsInvInvariant := hμMi
  let : ν.IsInvInvariant := hνi
  let : κ.IsInvInvariant := hκi
  let invAll (p : (M B × U B) × K n) := ((p.1.1⁻¹, p.1.2⁻¹), p.2⁻¹)
  have hInv : MeasurePreserving invAll ((μM.prod ν).prod κ) ((μM.prod ν).prod κ) :=
    ((measurePreserving_inv μM).prod (measurePreserving_inv ν)).prod (measurePreserving_inv κ)
  have hComp : Inv.inv ∘ leviRadicalUnitary B = unitaryRadicalLevi B ∘ invAll := by
    funext p
    simp only [Function.comp_apply, leviRadicalUnitary, unitaryRadicalLevi, invAll,
      mul_inv_rev, Subgroup.coe_inv, map_inv, mul_assoc]
  have hRight := congrArg (Measure.map (Inv.inv : G n → G n)) hLeft
  rwa [map_inv_eq_self, Measure.map_smul c measurable_inv.aemeasurable, Measure.map_map measurable_inv (continuous_leviRadicalUnitary B).measurable,
    hComp, ← Measure.map_map (continuous_unitaryRadicalLevi B).measurable hInv.measurable, hInv.map_eq] at hRight

end Langlands.Global.RankinSelbergGlobal.ComplexParabolicHaar
