import Langlands.Geometry.Analytic.SingleFiniteProductPieces
import Langlands.Geometry.Analytic.RecognizedImageNeighborhoods
import Langlands.Geometry.Analytic.FiniteProductNeighborhoods
import Langlands.Geometry.Analytic.FullRecognitionFiniteTargetLocalityStatement

/-! # Actual finite target neighborhood data for the small product projection -/

noncomputable section

universe u v

namespace Langlands.Analytic.AffinoidAtlasPresentation.StrongHom

open CategoryTheory Set Topology Filter PresentedAffinoidAlgebra IndexedAffinoidAtlas
open scoped Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : AffinoidAtlasPresentation.{u, v, v} K}
  (f : StrongHom A.saturatedPresentation C.saturatedPresentation)
  (g : StrongHom B.saturatedPresentation C.saturatedPresentation)
  [Small.{v} (FibreProduct.chartSystem f.compatibleRecognitionMap g.compatibleRecognitionMap).Space]

/-- The actual canonical same-universe product presentation of the selected cospan. -/
abbrev recognitionSmallProductPresentation :=
  FibreProduct.smallPresentation f.compatibleRecognitionMap g.compatibleRecognitionMap
    f.recognitionSource_hasAllLocalDomains g.recognitionSource_hasAllLocalDomains
    C.fullRecognitionPresentation_hasAllLocalDomains

/-- The existing compatible second projection of the canonical small product. -/
abbrev recognitionSmallSnd :=
  FibreProduct.smallSndHom f.compatibleRecognitionMap g.compatibleRecognitionMap
    f.recognitionSource_hasAllLocalDomains g.recognitionSource_hasAllLocalDomains
    C.fullRecognitionPresentation_hasAllLocalDomains

namespace FiniteProductNeighborhood

variable {f g}
  {Q : ∀ ⦃S T : PresentedAffinoidAlgebra K⦄, BoundedAlgHom K S T → BanachSpectrum T → Prop}
  {y : A.space} {z : B.space} (N : FiniteProductNeighborhood Q f g y z)

/-- The actual simultaneous open source neighborhood in the canonical small product. -/
def smallSourceNeighborhood : Set (recognitionSmallProductPresentation f g).space :=
  (FibreProduct.smallFstBase f.compatibleRecognitionMap g.compatibleRecognitionMap
    f.recognitionSource_hasAllLocalDomains g.recognitionSource_hasAllLocalDomains
    C.fullRecognitionPresentation_hasAllLocalDomains) ⁻¹' N.leftOpen ∩
      (recognitionSmallSnd f g).baseMap ⁻¹' N.rightPatch

theorem smallSourceNeighborhood_open : IsOpen N.smallSourceNeighborhood :=
  (N.leftOpen_open.preimage (FibreProduct.smallFstBase f.compatibleRecognitionMap g.compatibleRecognitionMap
    f.recognitionSource_hasAllLocalDomains g.recognitionSource_hasAllLocalDomains
    C.fullRecognitionPresentation_hasAllLocalDomains).continuous).inter
      (N.rightPatch_open.preimage (recognitionSmallSnd f g).baseMap.continuous)

variable [Nonempty (FibreProduct.LocalAtlasIndex f.compatibleRecognitionMap g.compatibleRecognitionMap)]

/-- At every target point there is a finite pointed recognized neighborhood
family with ACTUAL recognized whole preimages and finite original pullbacks. -/
theorem smallFiniteTargetFamily (hpush : AffinoidPushout.FiniteBanachPushoutStatement K) :
    ∀ x ∈ N.rightPatch,
      ∃ I : Set g.recognitionSource.atlas.saturatedAtlas.RecognizedSubset,
        I.Finite ∧
        (∀ W ∈ I, x ∈ W.locus ∧ W.locus ⊆ N.rightPatch ∧
          ∃ (P : (recognitionSmallProductPresentation f g).atlas.saturatedAtlas.RecognizedSubset)
            (h : (recognitionSmallSnd f g).saturationExtension.baseMap '' range P.chart ⊆ range W.chart),
            P.locus = N.smallSourceNeighborhood ∩
              (recognitionSmallSnd f g).saturationExtension.baseMap ⁻¹' W.locus ∧
            ((recognitionSmallSnd f g).saturationExtension.fullRecognitionPairs.pullback P W h).IsFiniteBanach) ∧
        (⋃ W ∈ I, W.locus) ∈ 𝓝 x := by
  classical
  intro x hx
  let _ : T2Space N.leftPatch := N.leftPatch_t2
  let _ : T2Space N.rightPatch := N.rightPatch_t2
  let F := g.recognizedImageNeighborhoods N.rightPatch N.rightPatch_open hx
    N.baseOpen N.baseOpen_open (N.right_baseOpen ⟨x, hx, rfl⟩)
  let _ := F.finite.fintype
  let D (R : F.family) := singleFiniteProductPiece N.finite R.val (F.target R.val R.property)
    (F.target_subset R.val R.property) (F.image R.val R.property)
  let H (R : F.family) := (D R).targetRecognition
  let I := range H
  refine ⟨I, Set.finite_range H, ?_, ?_⟩
  · rintro W ⟨R, rfl⟩
    have hR := (F.source R.val R.property).2
    have htarget := (D R).targetRecognition_locus
    refine ⟨htarget.symm ▸ (F.source R.val R.property).1, htarget.subset.trans hR, ?_⟩
    let P := (D R).smallRecognizedPreimage N.leftPatch N.rightPatch N.leftPatch_open N.rightPatch_open
      N.left_subset hR
    let h := FibreProduct.smallGoodPair_recognized_admissible
      f.compatibleRecognitionMap g.compatibleRecognitionMap
      f.recognitionSource_hasAllLocalDomains g.recognitionSource_hasAllLocalDomains
      C.fullRecognitionPresentation_hasAllLocalDomains (D R).pairIndex
      ((D R).pairIndex_good N.leftPatch N.rightPatch N.leftPatch_open N.rightPatch_open N.left_subset hR)
    refine ⟨P, h, ?_, (D R).actualPullback_isFiniteBanach N.leftPatch N.rightPatch
      N.leftPatch_open N.rightPatch_open N.left_subset hR hpush⟩
    apply ((D R).smallRecognizedPreimage_locus N.leftPatch N.rightPatch N.leftPatch_open N.rightPatch_open
      N.left_subset hR).trans
    ext t
    constructor
    · intro ht
      exact ⟨⟨ht.1, hR ht.2⟩, htarget.symm ▸ ht.2⟩
    · rintro ⟨⟨ht, -⟩, hW⟩
      exact ⟨ht, htarget ▸ hW⟩
  · apply Filter.mem_of_superset F.neighborhood
    rintro t ht
    obtain ⟨R, hR, htR⟩ := mem_iUnion₂.mp ht
    exact mem_iUnion₂.mpr ⟨H ⟨R, hR⟩, ⟨⟨R, hR⟩, rfl⟩,
      (D ⟨R, hR⟩).targetRecognition_locus.symm ▸ htR⟩

/-- The general target-locality criterion assembles the constructed actual
finite neighborhood pieces into global finite-over data. The criterion
is an explicit input, not a theorem supplied by this module. -/
theorem smallSnd_isFiniteOver
    (hlocal : FiniteOverTargetLocalityStatement.{u, v, v} K)
    (hpush : AffinoidPushout.FiniteBanachPushoutStatement K) :
    (recognitionSmallSnd f g).saturationExtension.IsFiniteOver
      N.smallSourceNeighborhood N.rightPatch :=
  hlocal (recognitionSmallProductPresentation f g) g.recognitionSource
    (recognitionSmallSnd f g).saturationExtension N.smallSourceNeighborhood N.rightPatch
    N.smallSourceNeighborhood_open N.rightPatch_open
    (fun _ ⟨_x, hx, hx'⟩ => hx' ▸ hx.2) (N.smallFiniteTargetFamily hpush)

/-- From a genuine all-pieces etale first neighborhood, the actual small
second projection has finite etale pieces at the corresponding quotient
point. Only the general target-local finiteness criterion is assumed. -/
theorem smallSnd_hasFiniteEtalePieces
    {y : A.space} {z : B.space}
    (N : FiniteProductNeighborhood (fun _ _ a s => a.IsEtaleAtPoint s) f g y z)
    (hlocal : FiniteOverTargetLocalityStatement.{u, v, v} K)
    (hpush : AffinoidPushout.FiniteBanachPushoutStatement K)
    (htensor : AffinoidPushout.FiniteTensorComparisonStatement K)
    (t : (recognitionSmallProductPresentation f g).space)
    (hy : FibreProduct.smallFstBase f.compatibleRecognitionMap g.compatibleRecognitionMap
      f.recognitionSource_hasAllLocalDomains g.recognitionSource_hasAllLocalDomains
      C.fullRecognitionPresentation_hasAllLocalDomains t = y)
    (hz : (recognitionSmallSnd f g).baseMap t = z) :
    (recognitionSmallSnd f g).saturationExtension.HasFinitePiecesAt
      (fun _ _ a s => a.IsEtaleAtPoint s) t := by
  classical
  let _ : T2Space N.leftPatch := N.leftPatch_t2
  let _ : T2Space N.rightPatch := N.rightPatch_t2
  have ht : t ∈ N.smallSourceNeighborhood := ⟨hy.symm ▸ N.mem_left, hz.symm ▸ N.mem_right⟩
  refine ⟨N.smallSourceNeighborhood, N.rightPatch, N.smallSourceNeighborhood_open,
    N.rightPatch_open, ht, N.smallSnd_isFiniteOver hlocal hpush, ?_⟩
  let F := g.recognizedImageNeighborhoods N.rightPatch N.rightPatch_open N.mem_right
    N.baseOpen N.baseOpen_open (N.right_baseOpen ⟨z, N.mem_right, rfl⟩)
  let _ := F.finite.fintype
  let D (R : F.family) := singleFiniteProductPiece N.finite R.val (F.target R.val R.property)
    (F.target_subset R.val R.property) (F.image R.val R.property)
  let H (R : F.family) := (D R).targetRecognition
  let I := range H
  have hIN : (⋃ W ∈ I, W.locus) ∈ 𝓝 z := by
    apply Filter.mem_of_superset F.neighborhood
    rintro x hx
    obtain ⟨R, hR, hxR⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion₂.mpr ⟨H ⟨R, hR⟩, ⟨⟨R, hR⟩, rfl⟩,
      (D ⟨R, hR⟩).targetRecognition_locus.symm ▸ hxR⟩
  refine ⟨I, Set.finite_range H, ?_, hz.symm ▸ hIN, ?_⟩
  · rintro W ⟨R, rfl⟩
    exact ⟨(D R).targetRecognition_locus.subset.trans (F.source R.val R.property).2,
      hz.symm ▸ ((D R).targetRecognition_locus.symm ▸ (F.source R.val R.property).1)⟩
  · rintro W ⟨R, rfl⟩ P hP hPlocus s hs
    have hR := (F.source R.val R.property).2
    let P₀ := (D R).smallRecognizedPreimage N.leftPatch N.rightPatch N.leftPatch_open N.rightPatch_open
      N.left_subset hR
    have hP₀ : P₀.locus = N.smallSourceNeighborhood ∩
        (recognitionSmallSnd f g).saturationExtension.baseMap ⁻¹' (H R).locus := by
      apply ((D R).smallRecognizedPreimage_locus N.leftPatch N.rightPatch N.leftPatch_open N.rightPatch_open
        N.left_subset hR).trans
      ext x
      constructor
      · intro hx
        exact ⟨⟨hx.1, hR hx.2⟩, (D R).targetRecognition_locus.symm ▸ hx.2⟩
      · rintro ⟨⟨hx, -⟩, hxR⟩
        exact ⟨hx, (D R).targetRecognition_locus ▸ hxR⟩
    have hPP₀ : P = P₀ := Subtype.ext (Subtype.ext (hPlocus.trans hP₀.symm))
    subst P
    have hyz : f.baseMap y = g.baseMap z :=
      (congrArg f.baseMap hy).symm.trans
        ((FibreProduct.baseMap_fst f.compatibleRecognitionMap g.compatibleRecognitionMap
          ((recognitionProductShrink f g).symm t)).trans (congrArg g.baseMap hz))
    have hbase : f.baseMap y ∈ (F.target R.val R.property).locus :=
      hyz.symm ▸ (F.image R.val R.property) ⟨z, (F.source R.val R.property).1, rfl⟩
    have hQ := N.allPieces (F.target R.val R.property) (F.target_subset R.val R.property) hbase
      (D R).left (D R).left_admissible (D R).left_locus
    exact (D R).actualPullback_isEtaleAtPoint_of_first_image N.leftPatch N.rightPatch
      N.leftPatch_open N.rightPatch_open N.left_subset hR hpush htensor y hQ s
        ((congrArg (fun x => FibreProduct.fst f.compatibleRecognitionMap g.compatibleRecognitionMap
          ((recognitionProductShrink f g).symm x)) hs).trans hy)

end FiniteProductNeighborhood
end Langlands.Analytic.AffinoidAtlasPresentation.StrongHom
