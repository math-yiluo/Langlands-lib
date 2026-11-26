import Langlands.Analysis.Local.WeightedProductChart
import Langlands.BaseChange.WeylTorusAffineHaar

/-! # Transport of rational torus Haar coordinates -/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory MeasureTheory.Measure Set _root_.Topology Langlands.Analysis
  Langlands.JacquetLanglands
open scoped NNReal

universe u v

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {E : Type v} [CommRing E] [Algebra F E] [TopologicalSpace E] [IsTopologicalRing E]
  [IsModuleTopology F E] {σ : E ≃ₐ[F] E} {l n : ℕ}
  (T : WeylTorus F n) (hσ : IsCyclicAlgebra σ l)

local notation "H" => T.val.map (baseChange F E n)

/-- Coefficient extension is a topological group isomorphism onto the rational
 torus image in the scalar-extended group. -/
def WeylTorus.baseChangeEquiv [T2Space E] : T.val ≃ₜ* H := by
  have hc := hσ.isClosedEmbedding_baseChange n
  let e := T.val.equivMapOfInjective (baseChange F E n) hc.injective
  have he : IsEmbedding e := IsEmbedding.subtypeVal.of_comp_iff.mp
    (hc.isEmbedding.comp IsEmbedding.subtypeVal)
  let e' := e.toEquiv.toHomeomorphOfIsInducing he.isInducing
  exact { e with continuous_toFun := e'.continuous, continuous_invFun := e'.symm.continuous }

@[simp]
theorem WeylTorus.baseChangeEquiv_val [T2Space E] (t : T.val) :
    (T.baseChangeEquiv hσ t).val = baseChange F E n t.val := rfl

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [IsTopologicalRing E] [IsModuleTopology F E] in
/-- The given equality of ambient pushforwards identifies the two torus measures
under any topological group isomorphism implementing coefficient extension. -/
theorem WeylTorus.map_baseChangeEquiv [T2Space E]
    [MeasurableSpace (GeneralLinear n F)] [BorelSpace (GeneralLinear n F)]
    [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)]
    (e : T.val ≃ₜ* H) (he : ∀ t, (e t).val = baseChange F E n t.val)
    (hH : IsClosed (H : Set (GeneralLinear n E)))
    (μT : Measure T.val) (μH : Measure H)
    (hμ : μH.map Subtype.val = μT.map (fun t : T.val => baseChange F E n t.val)) :
    μT.map e = μH := by
  have hsub : MeasurableEmbedding (Subtype.val : H → GeneralLinear n E) :=
    .subtype_coe hH.measurableSet
  have hme : Measurable e := e.continuous.measurable
  apply hsub.map_injective
  rw [Measure.map_map hsub.measurable hme, hμ]
  exact congrArg (fun f => μT.map f) (funext he)

section Chart

variable {a : GeneralLinear n F} (hT : glCentralizer a = T.val)
  [MeasurableSpace (GeneralLinear n F)] [BorelSpace (GeneralLinear n F)]
  [MeasurableSpace (weylTorusLie a)] [BorelSpace (weylTorusLie a)]

local notation "A" => WeylTorus.regularNormPoints T σ l
local notation "S" => weylTorusLie a

omit [TopologicalSpace E] [IsTopologicalRing E] [IsModuleTopology F E] in
/-- Restrict the rational affine chart and translate it into the regular
norm domain, retaining the exact Haar scale. -/
theorem WeylTorus.exists_regularNormAffineHaar
    (ha : IsRegularSemisimple a) (μT : Measure T.val) [μT.IsHaarMeasure] (ξ : Measure S) (c : ℝ≥0)
    (U : OpenSubgroup T.val) {B : Set S} (hB : T.affineCoordinate hT '' (U : Set T.val) = B)
    (hμT : (μT.restrict (U : Set T.val)).map (T.affineCoordinate hT) = c • ξ.restrict B)
    (t₀ : A) (hA : IsOpen (A : Set T.val))
    (hU : ∀ u ∈ (U : Set T.val), u * t₀.val ∈ A) :
    ∃ t : B → A, IsOpenEmbedding t ∧
      (∀ x, (t x).val.val.val = (1 + x.val.val) * t₀.val.val.val) ∧
      (c • ξ.comap Subtype.val).map t = (μT.comap Subtype.val).restrict (range t) := by
  let : T2Space F := LocalFieldTopology.t2Space F
  let : SecondCountableTopology F := LocalFieldTopology.secondCountableTopology F
  let : SecondCountableTopology (GeneralLinear n F) :=
    LocalFieldTopology.generalLinear_secondCountableTopology F n
  let : SecondCountableTopology T.val := IsEmbedding.subtypeVal.secondCountableTopology
  let : SecondCountableTopology S := by
    let : SecondCountableTopology (Matrix (Fin n) (Fin n) F) :=
      inferInstanceAs (SecondCountableTopology (Fin n → Fin n → F))
    exact IsEmbedding.subtypeVal.secondCountableTopology
  let aT := T.affineCoordinate hT
  have aE : IsOpenEmbedding aT := T.isOpenEmbedding_affineCoordinate hT
  have hBo : IsOpen B := hB ▸ aE.isOpenMap _ U.isOpen
  let e : U ≃ₜ B := (aE.isEmbedding.homeomorphImage (U : Set T.val)).trans (Homeomorph.setCongr hB)
  let m := Homeomorph.mulRight t₀.val
  let g : B → T.val := fun x => m (e.symm x).val
  let t : B → A := fun x => ⟨g x, hU (e.symm x).val (e.symm x).property⟩
  have hAg : IsOpenEmbedding (Subtype.val : A → T.val) := hA.isOpenEmbedding_subtypeVal
  have hg : IsOpenEmbedding g :=
    m.isOpenEmbedding.comp (U.isOpen.isOpenEmbedding_subtypeVal.comp e.symm.isOpenEmbedding)
  have ht : IsOpenEmbedding t := IsOpenEmbedding.of_comp t hAg hg
  refine ⟨t, ht, ?_, ?_⟩
  · intro x
    have he := congrArg (fun y : B => y.val.val) (e.apply_symm_apply x)
    change (e.symm x).val.val.val - 1 = x.val.val at he
    change (e.symm x).val.val.val * t₀.val.val.val = _
    rw [eq_add_of_sub_eq' he]
  have ham : Measurable aT := aE.continuous.measurable
  let k : B → T.val := fun x => (e.symm x).val
  have hk : Measurable k := (continuous_subtype_val.comp e.symm.continuous).measurable
  have hka : aT ∘ k = (Subtype.val : B → S) :=
    funext fun x => congrArg Subtype.val (e.apply_symm_apply x)
  have hκ : (c • ξ.comap (Subtype.val : B → S)).map k = μT.restrict (U : Set T.val) := by
    apply aE.measurableEmbedding.map_injective
    rw [Measure.map_map ham hk, hka, hμT, Measure.map_smul _ measurable_subtype_coe.aemeasurable,
      map_comap_subtype_coe hBo.measurableSet]
  let : IsMulRightInvariant μT := T.isMulRightInvariant_of_isHaarMeasure μT
  have hμm : μT.map m = μT := map_mul_right_eq_self μT t₀.val
  have hgr : range g = m '' (U : Set T.val) := by
    rw [show g = m ∘ (Subtype.val : U → T.val) ∘ e.symm from rfl,
      range_comp, range_comp, e.symm.surjective.range_eq, image_univ, Subtype.range_coe]
  have hμg : (c • ξ.comap (Subtype.val : B → S)).map g = μT.restrict (range g) := by
    have hgr' : range (m ∘ k) = m '' (U : Set T.val) := hgr
    rw [show g = m ∘ k from rfl, ← Measure.map_map m.continuous.measurable hk, hκ,
      map_restrict_image_of_embedding m.measurableEmbedding, hμm, hgr']
  have him : (Subtype.val : A → T.val) '' range t = range g := by
    rw [← range_comp]
    rfl
  apply hAg.measurableEmbedding.map_injective
  rw [Measure.map_map hAg.continuous.measurable ht.continuous.measurable,
    show (Subtype.val : A → T.val) ∘ t = g from rfl, hμg,
    map_restrict_image_of_embedding hAg.measurableEmbedding,
    map_comap_subtype_coe hA.measurableSet, him, Measure.restrict_restrict hg.isOpen_range.measurableSet,
    inter_eq_self_of_subset_left]
  rintro _ ⟨x, rfl⟩
  exact (t x).property

end Chart
end Langlands.BaseChange
