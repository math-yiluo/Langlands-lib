import Langlands.Representation.Plancherel.DynamicRepresentedGalleryOperators
import Langlands.Representation.Plancherel.DynamicCommonLeviContinuation
import Langlands.Representation.Plancherel.ParabolicOppositeQuotient

/-! # The represented complement chart of the actual pair quotient -/

noncomputable section

universe u

set_option quotPrecheck false

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel.DynamicCommonLeviPresentations

open Aubert.General Induction Aubert.General.RepresentedParabolic Haar
open DynamicOppositeStandardIntertwining DynamicCommonLeviComposition
open DynamicCommonLeviPresentationComparison DynamicCommonLeviStructuralComparison
open StandardIntertwining StandardIntertwining.OrderedSubgroupFactorization QuotientIntegration

private theorem exists_scaled_measurePreserving_complement
    {L W : Type u} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
    [LocallyCompactSpace L] [Group W] [TopologicalSpace W] [MeasurableSpace W] [BorelSpace W]
    (H C : Subgroup L) (m : H × C ≃ₜ L) (hm : ∀ v : H × C, m v = v.1.val * v.2.val)
    [MeasurableSpace C] [BorelSpace C]
    [MeasurableSpace (Induction.LeftQuotient H)] [BorelSpace (Induction.LeftQuotient H)]
    (e : C ≃ₜ* W) (μC : Measure C) [μC.IsHaarMeasure] [μC.Regular] [μC.IsMulRightInvariant]
    (μW : Measure W) (ν : Measure (Induction.LeftQuotient H)) [ν.Regular]
    (hν : ∀ v : L, MeasurePreserving (rightTranslate H v) ν ν) (hν0 : ν ≠ 0)
    (hμ : MeasurePreserving e μC μW) :
    ∃ s : ℝ≥0, 0 < s ∧
      MeasurePreserving (e.symm.toHomeomorph.trans (factorQuotientHomeomorph H Subtype.val m hm))
        (s • μW) ν := by
  let c := factorQuotientHomeomorph H Subtype.val m hm
  obtain ⟨s, hs⟩ := exists_smul_map_factorQuotientHomeomorph_symm H C m hm μC ν hν
  change Measure.map c.symm ν = s • μC at hs
  have hmap : Measure.map c (s • μC) = ν := by
    rw [← hs, Measure.map_map c.continuous.measurable c.symm.continuous.measurable,
      Homeomorph.self_comp_symm, Measure.map_id]
  have hspos : 0 < s := pos_iff_ne_zero.mpr (fun h0 => hν0 (by
    rw [h0, zero_smul, Measure.map_zero] at hmap
    exact hmap.symm))
  have hmeas : Measurable (e : C → W) := e.continuous.measurable
  have hmeas' : Measurable (e.symm : W → C) := e.symm.continuous.measurable
  have he' : Measure.map e.symm μW = μC := by
    rw [← hμ.map_eq, Measure.map_map hmeas' hmeas, show ⇑e.symm ∘ ⇑e = id from
      funext e.symm_apply_apply, Measure.map_id]
  refine ⟨s, hspos, ⟨(e.symm.toHomeomorph.trans c).continuous.measurable, ?_⟩⟩
  change Measure.map (c ∘ e.symm) (s • μW) = ν
  rw [← Measure.map_map c.continuous.measurable hmeas',
    Measure.map_smul _ hmeas'.aemeasurable, he', hmap]

private def subgroupOfInfEquivOfEq {L : Type u} [Group L] [TopologicalSpace L]
    {A B V : Subgroup L} (h : V = A ⊓ B) : A.subgroupOf B ≃ₜ* V :=
  (HarishChandraSchwartz.subgroupOfInfEquiv A B).trans (subgroupHomeomorphOfEq h.symm)

private theorem subgroupOfInfEquivOfEq_coe {L : Type u} [Group L] [TopologicalSpace L]
    {A B V : Subgroup L} (h : V = A ⊓ B) (v : A.subgroupOf B) :
    (subgroupOfInfEquivOfEq h v).val = v.val.val :=
  subgroupHomeomorphOfEq_coe _ _

private theorem subgroupOfInfEquivOfEq_measurePreserving
    {L : Type u} [Group L] [TopologicalSpace L] [IsTopologicalGroup L] [LocallyCompactSpace L]
    {A B V : Subgroup L} [MeasurableSpace (A.subgroupOf B)] [BorelSpace (A.subgroupOf B)]
    [MeasurableSpace V] [BorelSpace V]
    (hV : V = A ⊓ B) (hAc : IsClosed (A : Set L)) (hBc : IsClosed (B : Set L))
    (hVc : IsClosed (V : Set L)) (K : OpenSubgroup L) (hK : IsCompact (K : Set L)) :
    MeasurePreserving (subgroupOfInfEquivOfEq hV) (sourceIntersectionHaar K hK A B hAc hBc)
      (subgroupCompactOpenHaar K hK V hVc) :=
  measurePreserving_compactOpenHaarAlong K hK (intersectionAmbientHom A B)
    (intersectionAmbientHom_isClosedEmbedding A B hAc hBc) V.subtype hVc.isClosedEmbedding_subtypeVal
    (subgroupOfInfEquivOfEq hV) (subgroupOfInfEquivOfEq_coe hV)

attribute [local instance]
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsAffine
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsTopologicalGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarLocallyCompactSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  DynamicOppositeCanonicalScalar.centralizerClosedImmersion
  DynamicOppositeCanonicalScalar.centralizerAffine
  DynamicOppositeCanonicalScalar.centralizerFiniteType
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace2
  equalitySubgroupMeasurable equalitySubgroupBorel
  DynamicCommonLeviContinuation.intersectionMeasurable
  DynamicCommonLeviContinuation.intersectionBorel
  DynamicCommonLeviContinuation.quotientMeasurable
  DynamicCommonLeviContinuation.quotientBorel

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G}
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {a : T.toGrp ⟶ parameterScheme χ}
  (hG : IsConnectedReductive G) (ha : IsSplitComponent a)
  (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
  (x y : GalleryVertex χ)

local notation "d" => galleryVertexData hG ha
local notation "V" => representedComplement (d x.opposite) (d y)
local notation "Uᵧ" => radical y.val
local notation "H" => (radical x.val).subgroupOf Uᵧ
local notation "C" => (radical x.opposite.val).subgroupOf Uᵧ
local notation "Q" => QuotientSpace (U := radical x.val) Uᵧ
local notation "μV" => galleryPairHaar hG ha K hK x y
local notation "ν" => pairQuotientMeasure K hK x.val y.val

/-- The literal complement chart and the positive ratio of the two fixed measure scales. -/
structure GalleryQuotientChart where
  homeomorph : V ≃ₜ Q
  representative : ∀ v : V, ∃ u : Uᵧ, homeomorph v = Quotient.mk _ u ∧ u.val = v.val
  scale : ℝ≥0
  scale_pos : 0 < scale
  measurePreserving : MeasurePreserving homeomorph (scale • μV) ν

set_option maxHeartbeats 600000 in
private def galleryRadicalProduct :
    {m : H × C ≃ₜ Uᵧ // ∀ v : H × C, m v = v.1.val * v.2.val} :=
  Classical.choice (by
    have hProduct := exists_radical_product_homeomorph hG
      (d x).r.isCompatible.parabolic (d x).r.isCompatible.levi (d x).radical
      (d y).r.isCompatible.parabolic (d y).r.isCompatible.levi (d y).radical
      (multiplication_isIso hG (d y))
      (d x.opposite).r.isCompatible.parabolic (d x.opposite).r.isCompatible.levi (d x.opposite).radical
      ((d x).levi_comp.trans (d y).levi_comp.symm)
      ((d x.opposite).levi_comp.trans (d x).levi_comp.symm)
      (pointImage_inter_dynamicOpposite (d x) (d x.opposite) x.property)
    change ∃ m : ((pointImage ((d x).n ≫ (d x).p)).subgroupOf
          (pointImage ((d y).n ≫ (d y).p))) ×
        ((pointImage ((d x.opposite).n ≫ (d x.opposite).p) ⊓ pointImage ((d y).n ≫ (d y).p)).subgroupOf
          (pointImage ((d y).n ≫ (d y).p))) ≃ₜ pointImage ((d y).n ≫ (d y).p),
      ∀ v, m v = v.1.val * v.2.val at hProduct
    rw [pointImage_radical (d x), pointImage_radical (d y),
      pointImage_radical (d x.opposite), Subgroup.inf_subgroupOf_right] at hProduct
    obtain ⟨m, hm⟩ := hProduct
    exact ⟨⟨m, hm⟩⟩)

private def complementEquiv : C ≃ₜ* V :=
  subgroupOfInfEquivOfEq (representedComplement_eq (d x.opposite) (d y))

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
private theorem complementEquiv_coe (v : C) :
    (complementEquiv hG ha x y v).val = v.val.val :=
  subgroupOfInfEquivOfEq_coe (representedComplement_eq (d x.opposite) (d y)) v

local notation "μC" => sourceIntersectionHaar K hK (radical x.opposite.val) Uᵧ
  (radical_isClosed x.opposite.val) (radical_isClosed y.val)

set_option maxHeartbeats 600000 in
private theorem complementEquiv_measurePreserving :
    MeasurePreserving (complementEquiv hG ha x y) μC μV :=
  subgroupOfInfEquivOfEq_measurePreserving (representedComplement_eq (d x.opposite) (d y))
    (radical_isClosed x.opposite.val) (radical_isClosed y.val)
    (representedComplement_isClosed (d x.opposite) (d y)) K hK

set_option maxHeartbeats 800000 in
/-- Transport the actual quotient measure to the represented complement using radical multiplication. -/
def galleryQuotientChart : GalleryQuotientChart hG ha K hK x y :=
  Classical.choice (by
    let : LocallyCompactSpace Uᵧ := (radical_isClosed y.val).locallyCompactSpace
    let m := (galleryRadicalProduct hG ha x y).val
    have hm := (galleryRadicalProduct hG ha x y).property
    let c : C ≃ₜ Q := factorQuotientHomeomorph H Subtype.val m hm
    let e : C ≃ₜ* V := complementEquiv hG ha x y
    have hCover (v : radical x.opposite.val) :
        ∃ O : OpenSubgroup (radical x.opposite.val), IsCompact (O : Set (radical x.opposite.val)) ∧ v ∈ O := by
      obtain ⟨O, hO, hv⟩ := BruhatTits.DynamicUnipotentContainment.exists_compactOpenSubgroup
        x.opposite.val {v} isCompact_singleton
      exact ⟨O, hO, hv (Set.mem_singleton v)⟩
    let : (μC).IsMulRightInvariant :=
      sourceIntersectionHaar_rightInvariant_of_cover K hK (radical x.opposite.val) Uᵧ
        (radical_isClosed x.opposite.val) (radical_isClosed y.val) hCover
    have hν := pairQuotientMeasure_isCompatible K hK x.val y.val
    let : (ν).Regular := hν.regular
    obtain ⟨s, hspos, hμ⟩ := exists_scaled_measurePreserving_complement H C m hm e μC μV ν
      hν.right_invariant hν.nonzero (complementEquiv_measurePreserving hG ha K hK x y)
    let q : V ≃ₜ Q := e.symm.toHomeomorph.trans c
    refine ⟨⟨q, fun v => ⟨(e.symm v).val, rfl, ?_⟩, s, hspos, hμ⟩⟩
    exact (complementEquiv_coe hG ha x y (e.symm v)).symm.trans
      (congrArg Subtype.val (e.apply_symm_apply v)))

end Langlands.Plancherel.DynamicCommonLeviPresentations
