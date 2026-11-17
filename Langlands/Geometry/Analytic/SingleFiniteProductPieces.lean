import Langlands.Geometry.Analytic.SmallPairProjectionPullback
import Langlands.Geometry.Analytic.SmallFiniteOpenModelBinding

/-! # Whole finite preimages over a single recognized base chart -/

noncomputable section

universe u v

namespace Langlands.Analytic.FibreProduct

open Set PresentedAffinoidAlgebra AffinoidAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : AffinoidAtlasPresentation.{u, v, v} K}
  (f : CompatibleStrongHom A C) (g : CompatibleStrongHom B C)
  (p : PairIndex f g) (k : C.atlas.Index) (hk : IsCommonBase f g p.1.1 p.1.2 k)

include hk in
/-- An entire finite first preimage and an entire right chart over the
same base chart give the whole simultaneous preimage in the actual quotient. -/
theorem range_chart_of_left_preimage (V : Set A.space)
    (hV : range (A.atlas.chart p.1.1) = V ∩ f.baseMap ⁻¹' range (C.atlas.chart k)) :
    range ((chartSystem f g).chart p) =
      fst f g ⁻¹' V ∩ snd f g ⁻¹' range (B.atlas.chart p.1.2) := by
  ext x
  constructor
  · intro hx
    have hpair := (mem_range_chart_iff f g p x).1 hx
    exact ⟨(hV.subset hpair.1).1, hpair.2⟩
  · rintro ⟨hxV, hxR⟩
    apply (mem_range_chart_iff f g p x).2
    refine ⟨hV.symm.subset ⟨hxV, ?_⟩, hxR⟩
    change f.baseMap (fst f g x) ∈ range (C.atlas.chart k)
    exact (baseMap_fst f g x).symm ▸ hk.2 ⟨snd f g x, hxR, rfl⟩

end Langlands.Analytic.FibreProduct

namespace Langlands.Analytic.AffinoidAtlasPresentation.StrongHom

open CategoryTheory Set Topology PresentedAffinoidAlgebra IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : AffinoidAtlasPresentation.{u, v, v} K}
  {f : StrongHom A.saturatedPresentation C.saturatedPresentation}
  {g : StrongHom B.saturatedPresentation C.saturatedPresentation}

/-- One entire right recognized chart mapping to a single base chart,
together with the actual finite first preimage over that same chart. -/
structure SingleFiniteProductPiece
    (f : StrongHom A.saturatedPresentation C.saturatedPresentation)
    (g : StrongHom B.saturatedPresentation C.saturatedPresentation)
    (V : Set A.space) (R : B.atlas.saturatedAtlas.RecognizedSubset)
    (W : C.atlas.saturatedAtlas.RecognizedSubset) where
  left : A.atlas.saturatedAtlas.RecognizedSubset
  left_admissible : f.baseMap '' range left.chart ⊆ range W.chart
  left_locus : left.locus = V ∩ f.baseMap ⁻¹' W.locus
  left_finite : (f.fullRecognitionPairs.pullback left W left_admissible).IsFiniteBanach
  right_admissible : g.baseMap '' range R.chart ⊆ range W.chart

/-- Finiteness over the original open neighborhoods supplies the entire
single-chart piece, with no effective global algebra parent. -/
def singleFiniteProductPiece {V : Set A.space} {U : Set C.space}
    (hf : f.IsFiniteOver V U) (R : B.atlas.saturatedAtlas.RecognizedSubset)
    (W : C.atlas.saturatedAtlas.RecognizedSubset) (hWU : W.locus ⊆ U)
    (hR : g.baseMap '' R.locus ⊆ W.locus) : SingleFiniteProductPiece f g V R W :=
  let h := hf.2 W hWU
  { left := h.choose
    left_admissible := h.choose_spec.choose
    left_locus := h.choose_spec.choose_spec.1
    left_finite := h.choose_spec.choose_spec.2
    right_admissible := (image_mono R.range_chart.subset).trans (hR.trans W.range_chart.symm.subset) }

namespace SingleFiniteProductPiece

variable {V : Set A.space} {R : B.atlas.saturatedAtlas.RecognizedSubset}
  {W : C.atlas.saturatedAtlas.RecognizedSubset} (D : SingleFiniteProductPiece f g V R W)

/-- Both recognized factors are literal original indices of the selected cospan. -/
def pairIndex : FibreProduct.PairIndex f.compatibleRecognitionMap g.compatibleRecognitionMap :=
  ⟨(f.recognitionSourceIndex D.left W D.left_admissible,
    g.recognitionSourceIndex R W D.right_admissible), W, D.left_admissible, D.right_admissible⟩

theorem pairIndex_commonBase :
    FibreProduct.IsCommonBase f.compatibleRecognitionMap g.compatibleRecognitionMap
      D.pairIndex.1.1 D.pairIndex.1.2 W := ⟨D.left_admissible, D.right_admissible⟩

theorem range_pairIndex :
    range ((FibreProduct.chartSystem f.compatibleRecognitionMap g.compatibleRecognitionMap).chart D.pairIndex) =
      FibreProduct.fst f.compatibleRecognitionMap g.compatibleRecognitionMap ⁻¹' V ∩
        FibreProduct.snd f.compatibleRecognitionMap g.compatibleRecognitionMap ⁻¹' R.locus := by
  have hleft : range (f.recognitionSource.atlas.chart D.pairIndex.1.1) =
      V ∩ f.compatibleRecognitionMap.baseMap ⁻¹' range (C.fullRecognitionPresentation.atlas.chart W) :=
    D.left.range_chart.trans (D.left_locus.trans
      (congrArg (fun S : Set C.space => V ∩ f.baseMap ⁻¹' S) W.range_chart.symm))
  exact (FibreProduct.range_chart_of_left_preimage f.compatibleRecognitionMap g.compatibleRecognitionMap
    D.pairIndex W D.pairIndex_commonBase V hleft).trans
      (congrArg (fun S : Set B.space =>
        FibreProduct.fst f.compatibleRecognitionMap g.compatibleRecognitionMap ⁻¹' V ∩
          FibreProduct.snd f.compatibleRecognitionMap g.compatibleRecognitionMap ⁻¹' S) R.range_chart)

variable (OA : Set A.space) (OB : Set B.space) (hOA : IsOpen OA) (hOB : IsOpen OB)
  [hOAT : T2Space OA] [hOBT : T2Space OB] (hV : V ⊆ OA) (hR : R.locus ⊆ OB)

include hOA hOB hV hR hOAT hOBT in
theorem pairIndex_good :
    D.pairIndex ∈ FibreProduct.goodPairs f.compatibleRecognitionMap g.compatibleRecognitionMap :=
  ⟨OA, OB, hOA, hOB, hOAT, hOBT,
    D.left.range_chart.subset.trans (D.left_locus.subset.trans (inter_subset_left.trans hV)),
    R.range_chart.subset.trans hR⟩

variable [Small.{v} (FibreProduct.chartSystem f.compatibleRecognitionMap g.compatibleRecognitionMap).Space]
  [Nonempty (FibreProduct.LocalAtlasIndex f.compatibleRecognitionMap g.compatibleRecognitionMap)]

/-- The WHOLE small preimage is an actual recognized pair chart, with no
supplied parent or effectiveness premise for this single base chart. -/
def smallRecognizedPreimage : (recognitionSmallProductAtlas f g).saturatedAtlas.RecognizedSubset :=
  FibreProduct.smallGoodPairRecognition f.compatibleRecognitionMap g.compatibleRecognitionMap
    f.recognitionSource_hasAllLocalDomains g.recognitionSource_hasAllLocalDomains
    C.fullRecognitionPresentation_hasAllLocalDomains D.pairIndex (D.pairIndex_good OA OB hOA hOB hV hR)

theorem smallRecognizedPreimage_locus :
    (D.smallRecognizedPreimage OA OB hOA hOB hV hR).locus =
      (FibreProduct.fst f.compatibleRecognitionMap g.compatibleRecognitionMap ∘
        (recognitionProductShrink f g).symm) ⁻¹' V ∩
      (FibreProduct.snd f.compatibleRecognitionMap g.compatibleRecognitionMap ∘
        (recognitionProductShrink f g).symm) ⁻¹' R.locus := by
  have h := (FibreProduct.smallGoodPairRecognition_locus f.compatibleRecognitionMap g.compatibleRecognitionMap
    f.recognitionSource_hasAllLocalDomains g.recognitionSource_hasAllLocalDomains
    C.fullRecognitionPresentation_hasAllLocalDomains D.pairIndex (D.pairIndex_good OA OB hOA hOB hV hR)).trans
      (congrArg (fun S => (recognitionProductShrink f g) '' S) D.range_pairIndex)
  apply h.trans
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    change FibreProduct.fst f.compatibleRecognitionMap g.compatibleRecognitionMap
        ((recognitionProductShrink f g).symm ((recognitionProductShrink f g) x)) ∈ V ∧
      FibreProduct.snd f.compatibleRecognitionMap g.compatibleRecognitionMap
        ((recognitionProductShrink f g).symm ((recognitionProductShrink f g) x)) ∈ R.locus
    rw [Homeomorph.symm_apply_apply]
    exact hx
  · intro hz
    exact ⟨(recognitionProductShrink f g).symm z, hz, (recognitionProductShrink f g).apply_symm_apply z⟩

/-- The actual recognized whole right chart of the selected source atlas. -/
def targetRecognition : g.recognitionSource.atlas.saturatedAtlas.RecognizedSubset :=
  g.recognitionSource.atlas.recognizedLocalDomain
    (g.recognitionSource.atlas.originalLocalDomain D.pairIndex.1.2)

omit [Small.{v} (FibreProduct.chartSystem f.compatibleRecognitionMap g.compatibleRecognitionMap).Space]
  [Nonempty (FibreProduct.LocalAtlasIndex f.compatibleRecognitionMap g.compatibleRecognitionMap)] in
theorem targetRecognition_locus : D.targetRecognition.locus = R.locus :=
  (g.recognitionSource.atlas.recognizedLocalDomain_locus
    (g.recognitionSource.atlas.originalLocalDomain D.pairIndex.1.2)).trans
      ((g.recognitionSource.atlas.originalLocalDomain_locus D.pairIndex.1.2).trans R.range_chart)

/-- The existing full-recognition pullback of the actual small second
projection on this whole single-base-chart preimage. -/
abbrev actualPullback : BoundedAlgHom K D.targetRecognition.algebra
    (D.smallRecognizedPreimage OA OB hOA hOB hV hR).algebra :=
  FibreProduct.smallGoodPairFullPullback f.compatibleRecognitionMap g.compatibleRecognitionMap
    f.recognitionSource_hasAllLocalDomains g.recognitionSource_hasAllLocalDomains
    C.fullRecognitionPresentation_hasAllLocalDomains D.pairIndex (D.pairIndex_good OA OB hOA hOB hV hR)

theorem actualPullback_isFiniteBanach (hpush : AffinoidPushout.FiniteBanachPushoutStatement K) :
    (D.actualPullback OA OB hOA hOB hV hR).IsFiniteBanach :=
  FibreProduct.smallGoodPairFullPullback_isFiniteBanach f.compatibleRecognitionMap g.compatibleRecognitionMap
    f.recognitionSource_hasAllLocalDomains g.recognitionSource_hasAllLocalDomains
    C.fullRecognitionPresentation_hasAllLocalDomains D.pairIndex (D.pairIndex_good OA OB hOA hOB hV hR)
    hpush W D.pairIndex_commonBase D.left_finite

/-- The existing entire pullback is etale at every point where the
original finite first map is etale at its actual first-factor image. -/
theorem actualPullback_isEtaleAtPoint
    (hpush : AffinoidPushout.FiniteBanachPushoutStatement K)
    (htensor : AffinoidPushout.FiniteTensorComparisonStatement K)
    (x : BanachSpectrum (D.smallRecognizedPreimage OA OB hOA hOB hV hR).algebra)
    (hx : (f.fullRecognitionPairs.pullback D.left W D.left_admissible).IsEtaleAtPoint
      (FibreProduct.leftPoint f.compatibleRecognitionMap g.compatibleRecognitionMap D.pairIndex
        ((FibreProduct.smallGoodPairEquiv f.compatibleRecognitionMap g.compatibleRecognitionMap
          f.recognitionSource_hasAllLocalDomains g.recognitionSource_hasAllLocalDomains
          C.fullRecognitionPresentation_hasAllLocalDomains D.pairIndex
          (D.pairIndex_good OA OB hOA hOB hV hR)).spectrumHomeomorph x))) :
    (D.actualPullback OA OB hOA hOB hV hR).IsEtaleAtPoint x :=
  FibreProduct.smallGoodPairFullPullback_isEtaleAtPoint f.compatibleRecognitionMap g.compatibleRecognitionMap
    f.recognitionSource_hasAllLocalDomains g.recognitionSource_hasAllLocalDomains
    C.fullRecognitionPresentation_hasAllLocalDomains D.pairIndex (D.pairIndex_good OA OB hOA hOB hV hR)
    hpush htensor W D.pairIndex_commonBase D.left_finite x hx

/-- A certificate on the original first fiber is applied at the same
actual quotient point, using the complete recognized pair chart formula. -/
theorem actualPullback_isEtaleAtPoint_of_first_image
    (hpush : AffinoidPushout.FiniteBanachPushoutStatement K)
    (htensor : AffinoidPushout.FiniteTensorComparisonStatement K) (y : A.space)
    (hQ : ∀ s : BanachSpectrum D.left.algebra, D.left.chart s = y →
      (f.fullRecognitionPairs.pullback D.left W D.left_admissible).IsEtaleAtPoint s)
    (x : BanachSpectrum (D.smallRecognizedPreimage OA OB hOA hOB hV hR).algebra)
    (hx : FibreProduct.fst f.compatibleRecognitionMap g.compatibleRecognitionMap
      ((recognitionProductShrink f g).symm
        ((D.smallRecognizedPreimage OA OB hOA hOB hV hR).chart x)) = y) :
    (D.actualPullback OA OB hOA hOB hV hR).IsEtaleAtPoint x := by
  let q := FibreProduct.smallGoodPairEquiv f.compatibleRecognitionMap g.compatibleRecognitionMap
    f.recognitionSource_hasAllLocalDomains g.recognitionSource_hasAllLocalDomains
    C.fullRecognitionPresentation_hasAllLocalDomains D.pairIndex (D.pairIndex_good OA OB hOA hOB hV hR)
  have hchart := FibreProduct.smallGoodPairEquiv_chart f.compatibleRecognitionMap g.compatibleRecognitionMap
    f.recognitionSource_hasAllLocalDomains g.recognitionSource_hasAllLocalDomains
    C.fullRecognitionPresentation_hasAllLocalDomains D.pairIndex (D.pairIndex_good OA OB hOA hOB hV hR) x
  have hraw : (recognitionProductShrink f g).symm
      ((D.smallRecognizedPreimage OA OB hOA hOB hV hR).chart x) =
        (FibreProduct.chartSystem f.compatibleRecognitionMap g.compatibleRecognitionMap).chart D.pairIndex
          (q.spectrumHomeomorph x) :=
    (congrArg (recognitionProductShrink f g).symm hchart).trans
      ((recognitionProductShrink f g).symm_apply_apply _)
  exact D.actualPullback_isEtaleAtPoint OA OB hOA hOB hV hR hpush htensor x
    (hQ _ ((congrArg (FibreProduct.fst f.compatibleRecognitionMap g.compatibleRecognitionMap) hraw).symm.trans hx))

end SingleFiniteProductPiece
end Langlands.Analytic.AffinoidAtlasPresentation.StrongHom
