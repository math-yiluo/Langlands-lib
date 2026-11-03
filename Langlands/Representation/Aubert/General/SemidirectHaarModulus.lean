import Langlands.Representation.Aubert.General.Parabolic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Regular

/-! # Haar scaling in continuous semidirect coordinates -/

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped NNReal

namespace Langlands.Aubert.General.IsSemidirectDecomposition

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {P M U : Subgroup G} (h : IsSemidirectDecomposition P M U)
  (hp : Continuous h.projection)

/-- Multiplication in Levi-then-radical order is a homeomorphism. -/
def coordinates : M × U ≃ₜ P where
  toFun x := ⟨(x.1 : G) * (x.2 : G), P.mul_mem (h.levi_le x.1.2)
    (h.unipotent_le x.2.2)⟩
  invFun p := (h.projection p, ⟨(h.projection p : G)⁻¹ * (p : G),
    h.projection_inv_mul_mem p⟩)
  left_inv x := by
    have hm := h.projection_mul x.1 x.2
    apply Prod.ext
    · exact hm
    · apply Subtype.ext
      change (h.projection (⟨x.1, h.levi_le x.1.2⟩ *
        ⟨x.2, h.unipotent_le x.2.2⟩) : G)⁻¹ * ((x.1 : G) * (x.2 : G)) = (x.2 : G)
      rw [hm]
      simp
  right_inv p := by
    apply Subtype.ext
    exact mul_inv_cancel_left _ _
  continuous_toFun := by
    exact ((continuous_subtype_val.comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd)).subtype_mk _
  continuous_invFun := by
    exact hp.prodMk (((continuous_subtype_val.comp hp).inv.mul
      continuous_subtype_val).subtype_mk _)

@[simp]
theorem coordinates_apply (m : M) (u : U) :
    (h.coordinates hp (m, u) : G) = (m : G) * (u : G) := rfl

@[simp]
theorem coordinates_symm_fst (p : P) :
    ((h.coordinates hp).symm p).1 = h.projection p := rfl

@[simp]
theorem coordinates_symm_snd (p : P) :
    (((h.coordinates hp).symm p).2 : G) =
      (h.projection p : G)⁻¹ * (p : G) := rfl

/-- The radical translation in the left action on semidirect coordinates. -/
def leftCorrection (p : P) (m : M) : U :=
  ((h.coordinates hp).symm (p * h.coordinates hp (m, 1))).2

theorem continuous_leftCorrection (p : P) : Continuous (h.leftCorrection hp p) :=
  continuous_snd.comp ((h.coordinates hp).symm.continuous.comp
    (continuous_const.mul ((h.coordinates hp).continuous.comp
      (continuous_id.prodMk continuous_const))))

/-- Left multiplication has triangular form, with left translations in both fibers. -/
theorem coordinates_left_mul (p : P) (x : M × U) :
    (h.coordinates hp).symm (p * h.coordinates hp x) =
      (h.projection p * x.1, h.leftCorrection hp p x.1 * x.2) := by
  have hx : h.projection (h.coordinates hp x) = x.1 := h.projection_mul x.1 x.2
  have hx1 : h.projection (h.coordinates hp (x.1, 1)) = x.1 :=
    h.projection_mul x.1 1
  apply Prod.ext
  · change h.projection (p * h.coordinates hp x) = _
    rw [map_mul, hx]
  · apply Subtype.ext
    change (h.projection (p * h.coordinates hp x) : G)⁻¹ *
        ((p : G) * ((x.1 : G) * (x.2 : G))) =
      ((h.projection (p * h.coordinates hp (x.1, 1)) : G)⁻¹ *
        ((p : G) * ((x.1 : G) * (1 : G)))) * (x.2 : G)
    rw [map_mul, map_mul, hx, hx1]
    simp [mul_assoc]

section Measure

variable [SecondCountableTopology G]

local instance subgroupSecondCountable (H : Subgroup G) : SecondCountableTopology H :=
  TopologicalSpace.Subtype.secondCountableTopology (H : Set G)
local instance subgroupMeasurableSpace (H : Subgroup G) : MeasurableSpace H := borel H
local instance subgroupBorelSpace (H : Subgroup G) : BorelSpace H := ⟨rfl⟩
local instance productBorelSpace : BorelSpace (M × U) := Prod.borelSpace

theorem measurePreserving_coordinates_left_mul (μM : Measure M) (μU : Measure U)
    [μM.IsMulLeftInvariant] [μU.IsMulLeftInvariant] [SFinite μM] [SFinite μU]
    (p : P) :
    MeasurePreserving
      (fun x : M × U => (h.coordinates hp).symm (p * h.coordinates hp x))
      (μM.prod μU) (μM.prod μU) := by
  have hc : Continuous (fun x : M × U => h.leftCorrection hp p x.1 * x.2) :=
    ((h.continuous_leftCorrection hp p).comp continuous_fst).mul continuous_snd
  have ht := (measurePreserving_mul_left μM (h.projection p)).skew_product
    hc.measurable (Filter.Eventually.of_forall fun m =>
      (measurePreserving_mul_left μU (h.leftCorrection hp p m)).map_eq)
  convert ht using 1
  funext x
  exact h.coordinates_left_mul hp p x

/-- Product Haar measure in Levi-then-radical coordinates is left Haar on `P`. -/
theorem coordinates_isHaarMeasure (μM : Measure M) (μU : Measure U)
    [μM.IsHaarMeasure] [μU.IsHaarMeasure] [SFinite μM] [SFinite μU] :
    ((μM.prod μU).map (h.coordinates hp)).IsHaarMeasure := by
  let e := h.coordinates hp
  have he : Measurable (e : M × U → P) := e.continuous.measurable
  have : IsFiniteMeasureOnCompacts ((μM.prod μU).map e) :=
    IsFiniteMeasureOnCompacts.map (μM.prod μU) e
  have : IsOpenPosMeasure ((μM.prod μU).map e) :=
    e.continuous.isOpenPosMeasure_map e.surjective
  refine { map_mul_left_eq_self := fun p => ?_ }
  have ht := h.measurePreserving_coordinates_left_mul hp μM μU p
  have hm : Measurable (fun q : P => p * q) := (continuous_const.mul continuous_id).measurable
  rw [Measure.map_map hm he]
  have heq : (fun q : P => p * q) ∘ e =
      e ∘ (fun x : M × U => e.symm (p * e x)) := by
    funext x
    exact (e.apply_symm_apply _).symm
  rw [heq, ← Measure.map_map he ht.measurable, ht.map_eq]

variable [LocallyCompactSpace M] [LocallyCompactSpace U] [LocallyCompactSpace P]

/-- An automorphism respecting both semidirect factors has the product Haar modulus. -/
theorem haarChar_eq_mul (a : P ≃ₜ* P) (aM : M ≃ₜ* M) (aU : U ≃ₜ* U)
    (ha : ∀ (m : M) (u : U),
      a (h.coordinates hp (m, u)) = h.coordinates hp (aM m, aU u)) :
    mulEquivHaarChar a = mulEquivHaarChar aM * mulEquivHaarChar aU := by
  let μM : Measure M := haar
  let μU : Measure U := haar
  let μ : Measure (M × U) := μM.prod μU
  let e := h.coordinates hp
  let ν : Measure P := μ.map e
  have : ν.IsHaarMeasure := h.coordinates_isHaarMeasure hp μM μU
  have : ν.Regular := inferInstance
  have he : Measurable (e : M × U → P) := e.continuous.measurable
  have hA : Measurable (a : P → P) := a.continuous.measurable
  have hM : Measurable (aM : M → M) := aM.continuous.measurable
  have hU : Measurable (aU : U → U) := aU.continuous.measurable
  have hprod : (mulEquivHaarChar aM * mulEquivHaarChar aU) •
      μ.map (Prod.map aM aU) = μ := by
    change (mulEquivHaarChar aM * mulEquivHaarChar aU) •
      (μM.prod μU).map (Prod.map aM aU) = μM.prod μU
    rw [← Measure.map_prod_map μM μU hM hU]
    calc
      _ = (mulEquivHaarChar aM • μM.map aM).prod
          (mulEquivHaarChar aU • μU.map aU) := by
        rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
      _ = μM.prod μU := by
        rw [mulEquivHaarChar_smul_map μM aM, mulEquivHaarChar_smul_map μU aU]
  have hcoord : a ∘ e = e ∘ Prod.map aM aU := funext fun x => ha x.1 x.2
  have hscale : (mulEquivHaarChar aM * mulEquivHaarChar aU) • ν.map a = ν := by
    calc
      _ = ((mulEquivHaarChar aM * mulEquivHaarChar aU) •
          μ.map (Prod.map aM aU)).map e := by
        rw [Measure.map_smul _ he.aemeasurable]
        congr 1
        change (μ.map e).map a = (μ.map (Prod.map aM aU)).map e
        rw [Measure.map_map hA he, hcoord, ← Measure.map_map he (hM.prodMap hU)]
      _ = ν := by rw [hprod]
  rw [mulEquivHaarChar_eq ν]
  have hs := haarScalarFactor_smul (ν.map a) (ν.map a)
    (c := mulEquivHaarChar aM * mulEquivHaarChar aU)
  rw! [hscale] at hs
  simpa using hs

end Measure

end Langlands.Aubert.General.IsSemidirectDecomposition
