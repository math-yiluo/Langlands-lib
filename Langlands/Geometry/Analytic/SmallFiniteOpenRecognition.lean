import Langlands.Geometry.Analytic.SmallFiniteOpenModelBinding
import Langlands.Geometry.Analytic.FiniteProductNeighborhoods
import Langlands.Geometry.Analytic.FullRecognitionNaturality
import Langlands.Geometry.Analytic.QuasiIsoSourceEtale

/-! # Actual recognized finite preimages in the canonical small product -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas.FiniteChartGluingData.AffinoidRealization

open Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] {a : IndexedAffinoidAtlas.{u, v, w} K X}
  {d : FiniteChartGluingData a} (c : d.AffinoidRealization) [T2Space d.locus]

/-- Recognition of a realized parent preserves every entire defining
component restriction through the constructed bounded equivalence. -/
theorem originalRestriction_comp_recognitionEquiv (i : Fin d.size)
    (h : range (a.chart (d.index i)) ⊆ c.recognizedSubset.locus) :
    (c.recognizedSubset.originalRestriction (d.index i) h).comp
      c.recognitionEquiv.toBoundedAlgHom = c.restriction i := by
  have hc := c.recognizedSubset.originalRestriction_comp_affinoidRealization d rfl c
    (d.index i) h
  exact hc.trans ((congrArg (fun q : BoundedAlgHom K d.SectionAlgebra (a.algebra (d.index i)) =>
    q.comp c.restrictFromParent) (d.originalRestriction_index i _)).trans
      (c.projection_comp_restrictFromParent i))

/-- Equality on the entire defining component restrictions detects
bounded maps into the recognized parent, by finite-domain algebra separation. -/
theorem hom_ext_of_component_restrictions
    {S : PresentedAffinoidAlgebra K}
    {φ ψ : BoundedAlgHom K S c.recognizedSubset.algebra}
    (h : ∀ i : Fin d.size,
      (c.recognizedSubset.originalRestriction (d.index i)
        (fun _ hx => mem_iUnion.mpr ⟨i, hx⟩)).comp φ =
      (c.recognizedSubset.originalRestriction (d.index i)
        (fun _ hx => mem_iUnion.mpr ⟨i, hx⟩)).comp ψ) : φ = ψ := by
  apply BoundedAlgHom.ext
  intro x
  apply c.recognitionEquiv.symm.injective
  apply c.domainCover.algebra_ext_of_restrict_eq
  intro i
  have hi : range (a.chart (d.index i)) ⊆ c.recognizedSubset.locus :=
    fun _ hx => mem_iUnion.mpr ⟨i, hx⟩
  change (c.restriction i) (c.recognitionEquiv.symm (φ x)) =
    (c.restriction i) (c.recognitionEquiv.symm (ψ x))
  have he := c.originalRestriction_comp_recognitionEquiv i hi
  have hφ := congrArg (fun q : BoundedAlgHom K c.algebra (a.algebra (d.index i)) =>
    q (c.recognitionEquiv.symm (φ x))) he
  have hψ := congrArg (fun q : BoundedAlgHom K c.algebra (a.algebra (d.index i)) =>
    q (c.recognitionEquiv.symm (ψ x))) he
  change (c.recognizedSubset.originalRestriction (d.index i) hi)
      (c.recognitionEquiv (c.recognitionEquiv.symm (φ x))) =
    (c.restriction i) (c.recognitionEquiv.symm (φ x)) at hφ
  change (c.recognizedSubset.originalRestriction (d.index i) hi)
      (c.recognitionEquiv (c.recognitionEquiv.symm (ψ x))) =
    (c.restriction i) (c.recognitionEquiv.symm (ψ x)) at hψ
  rw [c.recognitionEquiv.apply_symm_apply] at hφ hψ
  exact hφ.symm.trans ((congrArg (fun q : BoundedAlgHom K S
    (a.algebra (d.index i)) => q x) (h i)).trans hψ)

end Langlands.Analytic.IndexedAffinoidAtlas.FiniteChartGluingData.AffinoidRealization

namespace Langlands.Analytic.AffinoidAtlasPresentation.StrongHom

open CategoryTheory Set Topology PresentedAffinoidAlgebra IndexedAffinoidAtlas
open FiniteAffinoidAlgebraDescent

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : AffinoidAtlasPresentation.{u, v, v} K}
  {f : StrongHom A.saturatedPresentation C.saturatedPresentation}
  {g : StrongHom B.saturatedPresentation C.saturatedPresentation}
  [Small.{v} (FibreProduct.chartSystem f.compatibleRecognitionMap g.compatibleRecognitionMap).Space]

namespace FiniteOpenBaseChangeModels

variable {V : Set A.space} {U : Set C.space} {R : B.atlas.saturatedAtlas.RecognizedSubset}
  (M : FiniteOpenBaseChangeModels f g V U R)
  (OA : Set A.space) (OB : Set B.space) (hOA : IsOpen OA) (hOB : IsOpen OB)
  [hOAT : T2Space OA] [hOBT : T2Space OB] (hV : V ⊆ OA) (hR : R.locus ⊆ OB)
  [Nonempty (FibreProduct.LocalAtlasIndex f.compatibleRecognitionMap g.compatibleRecognitionMap)]
  [hT : T2Space ↥(FibreProduct.fst f.compatibleRecognitionMap g.compatibleRecognitionMap ⁻¹' V ∩
    FibreProduct.snd f.compatibleRecognitionMap g.compatibleRecognitionMap ⁻¹' R.locus)]

/-- Only Hausdorffness of the entire literal preimage is needed; the
canonical space shrinking transfers it to the exact small gluing locus. -/
theorem smallChartBinding_t2 :
    T2Space (M.smallChartBinding OA OB hOA hOB hV hR).gluingData.locus := by
  have h := ((recognitionProductShrink f g).image
    (FibreProduct.fst f.compatibleRecognitionMap g.compatibleRecognitionMap ⁻¹' V ∩
      FibreProduct.snd f.compatibleRecognitionMap g.compatibleRecognitionMap ⁻¹' R.locus)).t2Space
  exact (M.smallChartBinding_locus OA OB hOA hOB hV hR).symm ▸ h

variable (P : EffectiveRealization M.algebraDescentData)

/-- An effective parent makes the entire small preimage intrinsically
recognized. No recognized parent or embedding is assumed. -/
def smallRecognizedPreimage : (recognitionSmallProductAtlas f g).saturatedAtlas.RecognizedSubset :=
  letI := M.smallChartBinding_t2 OA OB hOA hOB hV hR
  (M.smallChartBinding OA OB hOA hOB hV hR).recognizedSubset P

theorem smallRecognizedPreimage_locus :
    (M.smallRecognizedPreimage OA OB hOA hOB hV hR P).locus =
      (FibreProduct.fst f.compatibleRecognitionMap g.compatibleRecognitionMap ∘
        (recognitionProductShrink f g).symm) ⁻¹' V ∩
      (FibreProduct.snd f.compatibleRecognitionMap g.compatibleRecognitionMap ∘
        (recognitionProductShrink f g).symm) ⁻¹' R.locus :=
  M.smallChartBinding_locus_eq_preimage OA OB hOA hOB hV hR

/-- The entire effective parent algebra is retained in the recognized preimage. -/
def smallRecognitionEquiv : BoundedAlgEquiv K P.algebra
    (M.smallRecognizedPreimage OA OB hOA hOB hV hR P).algebra :=
  letI := M.smallChartBinding_t2 OA OB hOA hOB hV hR
  (M.smallChartBinding OA OB hOA hOB hV hR).recognitionEquiv P

/-- The finite bounded structural map from the original right affinoid. -/
def smallFiniteBaseMap : BoundedAlgHom K R.algebra
    (M.smallRecognizedPreimage OA OB hOA hOB hV hR P).algebra :=
  (M.smallRecognitionEquiv OA OB hOA hOB hV hR P).toBoundedAlgHom.comp
    P.toMatchingPresentation.baseMap

theorem smallFiniteBaseMap_isFiniteBanach :
    (M.smallFiniteBaseMap OA OB hOA hOB hV hR P).IsFiniteBanach :=
  (M.smallRecognitionEquiv OA OB hOA hOB hV hR P).isFiniteBanach.comp P.finite

theorem smallModelIndex_subset_smallRecognizedPreimage (i : Fin M.rightCover.cover.size) :
    range ((recognitionSmallProductAtlas f g).saturatedAtlas.chart
      (M.smallModelIndex OA OB hOA hOB hV hR i)) ⊆
        (M.smallRecognizedPreimage OA OB hOA hOB hV hR P).locus :=
  fun _ hx => mem_iUnion.mpr ⟨i, hx⟩

/-- Exact whole coefficient comparison on every original model chart. -/
theorem smallRecognitionEquiv_originalRestriction (i : Fin M.rightCover.cover.size)
    (hi : range ((recognitionSmallProductAtlas f g).saturatedAtlas.chart
      (M.smallModelIndex OA OB hOA hOB hV hR i)) ⊆
        (M.smallRecognizedPreimage OA OB hOA hOB hV hR P).locus) :
    ((M.smallRecognizedPreimage OA OB hOA hOB hV hR P).originalRestriction
      (M.smallModelIndex OA OB hOA hOB hV hR i) hi).comp
        (M.smallRecognitionEquiv OA OB hOA hOB hV hR P).toBoundedAlgHom =
      (M.smallModelEquiv OA OB hOA hOB hV hR i).toBoundedAlgHom.comp
        (P.toMatchingPresentation.localMap i) := by
  let _ := M.smallChartBinding_t2 OA OB hOA hOB hV hR
  exact ((M.smallChartBinding OA OB hOA hOB hV hR).affinoidRealization P).originalRestriction_comp_recognitionEquiv i hi

/-- The finite global structural map recovers the original entire right
structural leg on every unchanged local model. -/
theorem smallFiniteBaseMap_originalRestriction (i : Fin M.rightCover.cover.size)
    (hi : range ((recognitionSmallProductAtlas f g).saturatedAtlas.chart
      (M.smallModelIndex OA OB hOA hOB hV hR i)) ⊆
        (M.smallRecognizedPreimage OA OB hOA hOB hV hR P).locus) :
    ((M.smallRecognizedPreimage OA OB hOA hOB hV hR P).originalRestriction
      (M.smallModelIndex OA OB hOA hOB hV hR i) hi).comp
        (M.smallFiniteBaseMap OA OB hOA hOB hV hR P) =
      (M.smallModelEquiv OA OB hOA hOB hV hR i).toBoundedAlgHom.comp
        ((M.rightMap i).comp (M.rightCover.cover.obj i).baseMap) := by
  have hs : (P.toMatchingPresentation.localMap i).comp P.toMatchingPresentation.baseMap =
      (M.rightMap i).comp (M.rightCover.cover.obj i).baseMap :=
    (P.toMatchingPresentation.localMap_baseMap i).trans
      (M.descentLocalAlgebras.structuralMap_eq i)
  exact (BoundedAlgHom.comp_assoc _ _ _).symm.trans
    ((congrArg (fun q : BoundedAlgHom K P.algebra
      ((recognitionSmallProductAtlas f g).saturatedAtlas.algebra
        (M.smallModelIndex OA OB hOA hOB hV hR i)) =>
        q.comp P.toMatchingPresentation.baseMap)
      (M.smallRecognitionEquiv_originalRestriction OA OB hOA hOB hV hR P i hi)).trans
        ((BoundedAlgHom.comp_assoc _ _ _).trans
          (congrArg (fun q : BoundedAlgHom K R.algebra (M.algebra i) =>
            (M.smallModelEquiv OA OB hOA hOB hV hR i).toBoundedAlgHom.comp q) hs)))

/-- The constructed finite structural map is the unique complete bounded
map having the original right legs on every actual model chart. -/
theorem smallFiniteBaseMap_unique
    (φ : BoundedAlgHom K R.algebra
      (M.smallRecognizedPreimage OA OB hOA hOB hV hR P).algebra)
    (hφ : ∀ i : Fin M.rightCover.cover.size,
      ((M.smallRecognizedPreimage OA OB hOA hOB hV hR P).originalRestriction
        (M.smallModelIndex OA OB hOA hOB hV hR i)
        (M.smallModelIndex_subset_smallRecognizedPreimage OA OB hOA hOB hV hR P i)).comp φ =
      (M.smallModelEquiv OA OB hOA hOB hV hR i).toBoundedAlgHom.comp
        ((M.rightMap i).comp (M.rightCover.cover.obj i).baseMap)) :
    φ = M.smallFiniteBaseMap OA OB hOA hOB hV hR P := by
  let _ := M.smallChartBinding_t2 OA OB hOA hOB hV hR
  apply ((M.smallChartBinding OA OB hOA hOB hV hR).affinoidRealization P).hom_ext_of_component_restrictions
  intro i
  exact (hφ i).trans
    (M.smallFiniteBaseMap_originalRestriction OA OB hOA hOB hV hR P i _).symm

/-- The finite coefficient map has exactly the canonical second projection
on the complete recognized spectrum, by its proved entire component equations. -/
theorem smallFiniteBaseMap_chart
    (x : BanachSpectrum (M.smallRecognizedPreimage OA OB hOA hOB hV hR P).algebra) :
    R.chart (BanachSpectrum.comap (M.smallFiniteBaseMap OA OB hOA hOB hV hR P).toBoundedRingHom x) =
      FibreProduct.snd f.compatibleRecognitionMap g.compatibleRecognitionMap
        ((recognitionProductShrink f g).symm
          ((M.smallRecognizedPreimage OA OB hOA hOB hV hR P).chart x)) := by
  let W := M.smallRecognizedPreimage OA OB hOA hOB hV hR P
  have hx : W.chart x ∈ (M.smallChartBinding OA OB hOA hOB hV hR).gluingData.locus :=
    W.range_chart.subset ⟨x, rfl⟩
  change W.chart x ∈ ⋃ i : Fin M.rightCover.cover.size,
    range ((recognitionSmallProductAtlas f g).saturatedAtlas.chart
      (M.smallModelIndex OA OB hOA hOB hV hR i)) at hx
  obtain ⟨i, hi'⟩ := mem_iUnion.mp hx
  obtain ⟨t, ht⟩ := hi'
  let hi := M.smallModelIndex_subset_smallRecognizedPreimage OA OB hOA hOB hV hR P i
  have hxt : BanachSpectrum.comap
      (W.originalRestriction (M.smallModelIndex OA OB hOA hOB hV hR i) hi).toBoundedRingHom t = x :=
    W.isEmbedding_chart.injective
      ((W.chart_originalRestriction _ hi t).trans ht)
  have hmap := congrArg (fun q : BoundedAlgHom K R.algebra
    ((recognitionSmallProductAtlas f g).saturatedAtlas.algebra
      (M.smallModelIndex OA OB hOA hOB hV hR i)) =>
        BanachSpectrum.comap q.toBoundedRingHom t)
    (M.smallFiniteBaseMap_originalRestriction OA OB hOA hOB hV hR P i hi)
  have hchart := M.smallModelEquiv_chart OA OB hOA hOB hV hR i t
  have hraw : (recognitionProductShrink f g).symm (W.chart x) =
      M.productChart i ((M.smallModelEquiv OA OB hOA hOB hV hR i).spectrumHomeomorph t) :=
    (congrArg (recognitionProductShrink f g).symm
      (hchart.trans ht)).symm.trans
        ((recognitionProductShrink f g).symm_apply_apply _)
  exact (congrArg R.chart ((congrArg
    (BanachSpectrum.comap (M.smallFiniteBaseMap OA OB hOA hOB hV hR P).toBoundedRingHom)
      hxt).symm.trans hmap)).trans ((M.snd_productChart i _).symm.trans
        (congrArg (FibreProduct.snd f.compatibleRecognitionMap g.compatibleRecognitionMap) hraw).symm)

end FiniteOpenBaseChangeModels
namespace FiniteProductNeighborhood

variable {Q : ∀ ⦃S T : PresentedAffinoidAlgebra K⦄,
    BoundedAlgHom K S T → BanachSpectrum T → Prop}
  {y : A.space} {z : B.space} (N : FiniteProductNeighborhood Q f g y z)

/-- Genuine local Hausdorff product patches give separation on every entire
small finite preimage without a global ambient Hausdorff assumption. -/
theorem smallPreimage_t2 (R : B.atlas.saturatedAtlas.RecognizedSubset)
    (hR : R.locus ⊆ N.rightPatch) :
    T2Space ↥((FibreProduct.fst f.compatibleRecognitionMap g.compatibleRecognitionMap ∘
        (recognitionProductShrink f g).symm) ⁻¹' N.leftOpen ∩
      (FibreProduct.snd f.compatibleRecognitionMap g.compatibleRecognitionMap ∘
        (recognitionProductShrink f g).symm) ⁻¹' R.locus) := by
  let S := FibreProduct.fst f.compatibleRecognitionMap g.compatibleRecognitionMap ⁻¹' N.leftOpen ∩
    FibreProduct.snd f.compatibleRecognitionMap g.compatibleRecognitionMap ⁻¹' R.locus
  let _ : T2Space S := N.preimage_t2 R hR
  exact (((recognitionProductShrink f g).symm.isEmbedding.comp IsEmbedding.subtypeVal).codRestrict S
    (fun x => x.property)).t2Space

end FiniteProductNeighborhood
end Langlands.Analytic.AffinoidAtlasPresentation.StrongHom
