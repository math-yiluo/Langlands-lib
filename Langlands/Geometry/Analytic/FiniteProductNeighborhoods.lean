import Langlands.Geometry.Analytic.FiniteOpenModelGluing

/-! # Finite neighborhoods inside actual Hausdorff product patches -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation.StrongHom

open CategoryTheory Set Topology Filter PresentedAffinoidAlgebra IndexedAffinoidAtlas
open scoped Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : AffinoidAtlasPresentation.{u, v, w} K}
  {f : StrongHom A.saturatedPresentation C.saturatedPresentation}
  {g : StrongHom B.saturatedPresentation C.saturatedPresentation}
  {Q : ∀ ⦃R S : PresentedAffinoidAlgebra K⦄, BoundedAlgHom K R S → BanachSpectrum S → Prop}

/-- A finite all-pieces neighborhood together with actual open Hausdorff
factor patches mapping into one actual open Hausdorff base patch. -/
structure FiniteProductNeighborhood (Q :
    ∀ ⦃R S : PresentedAffinoidAlgebra K⦄, BoundedAlgHom K R S → BanachSpectrum S → Prop)
    (f : StrongHom A.saturatedPresentation C.saturatedPresentation)
    (g : StrongHom B.saturatedPresentation C.saturatedPresentation)
    (y : A.space) (z : B.space) where
  leftOpen : Set A.space
  baseOpen : Set C.space
  leftPatch : Set A.space
  rightPatch : Set B.space
  basePatch : Set C.space
  leftOpen_open : IsOpen leftOpen
  baseOpen_open : IsOpen baseOpen
  leftPatch_open : IsOpen leftPatch
  rightPatch_open : IsOpen rightPatch
  basePatch_open : IsOpen basePatch
  leftPatch_t2 : T2Space leftPatch
  rightPatch_t2 : T2Space rightPatch
  basePatch_t2 : T2Space basePatch
  mem_left : y ∈ leftOpen
  mem_right : z ∈ rightPatch
  left_subset : leftOpen ⊆ leftPatch
  left_image : f.baseMap '' leftPatch ⊆ basePatch
  right_image : g.baseMap '' rightPatch ⊆ basePatch
  right_baseOpen : g.baseMap '' rightPatch ⊆ baseOpen
  finite : f.IsFiniteOver leftOpen baseOpen
  allPieces : ∀ W : C.atlas.saturatedAtlas.RecognizedSubset,
    W.locus ⊆ baseOpen → f.baseMap y ∈ W.locus →
    ∀ (P : A.atlas.saturatedAtlas.RecognizedSubset)
      (h : f.baseMap '' range P.chart ⊆ range W.chart),
      P.locus = leftOpen ∩ f.baseMap ⁻¹' W.locus →
      ∀ s : BanachSpectrum P.algebra, P.chart s = y →
        Q (f.fullRecognitionPairs.pullback P W h) s

private theorem nonempty_finiteProductNeighborhood
    (hpost : ∀ ⦃R S T : PresentedAffinoidAlgebra K⦄
      (r : BoundedAlgHom K S T) (a : BoundedAlgHom K R S) (x : BanachSpectrum T),
      r.toAlgHom.toRingHom.Flat → Function.Surjective r →
      a.toAlgHom.toRingHom.FiniteType →
      Q a (BanachSpectrum.comap r.toBoundedRingHom x) → Q (r.comp a) x)
    {y : A.space} {z : B.space} (hf : f.HasAllPiecesAt Q y)
    (hyz : f.baseMap y = g.baseMap z) :
    Nonempty (FiniteProductNeighborhood Q f g y z) := by
  obtain ⟨OA, hOA, hyOA, hOAT⟩ := FibreProduct.exists_open_hausdorff_neighborhood A.atlas y
  obtain ⟨OB, hOB, hzOB, hOBT⟩ := FibreProduct.exists_open_hausdorff_neighborhood B.atlas z
  obtain ⟨OC, hOC, hyOC, hOCT⟩ :=
    FibreProduct.exists_open_hausdorff_neighborhood C.atlas (f.baseMap y)
  let LA := OA ∩ f.baseMap ⁻¹' OC
  have hLA : IsOpen LA := hOA.inter (hOC.preimage f.baseMap.continuous)
  have hLAT : T2Space LA := by
    let : T2Space OA := hOAT
    exact (IsEmbedding.subtypeVal.codRestrict OA (fun x : LA => x.property.1)).t2Space
  obtain ⟨V₀, U₀, hV₀, hU₀, hyV₀, hVLA, hfin₀, hQ₀⟩ :=
    hf.exists_small hpost (hLA.mem_nhds ⟨hyOA, hyOC⟩)
  let U := U₀ ∩ OC
  let V := V₀ ∩ f.baseMap ⁻¹' U
  let RB := OB ∩ g.baseMap ⁻¹' U
  have hU : IsOpen U := hU₀.inter hOC
  have hV : IsOpen V := hV₀.inter (hU.preimage f.baseMap.continuous)
  have hRB : IsOpen RB := hOB.inter (hU.preimage g.baseMap.continuous)
  have hRBT : T2Space RB := by
    let : T2Space OB := hOBT
    exact (IsEmbedding.subtypeVal.codRestrict OB (fun x : RB => x.property.1)).t2Space
  have hyU : f.baseMap y ∈ U := ⟨hfin₀.1 ⟨y, hyV₀, rfl⟩, hyOC⟩
  have hzU : g.baseMap z ∈ U := hyz ▸ hyU
  refine ⟨{
    leftOpen := V
    baseOpen := U
    leftPatch := LA
    rightPatch := RB
    basePatch := OC
    leftOpen_open := hV
    baseOpen_open := hU
    leftPatch_open := hLA
    rightPatch_open := hRB
    basePatch_open := hOC
    leftPatch_t2 := hLAT
    rightPatch_t2 := hRBT
    basePatch_t2 := hOCT
    mem_left := ⟨hyV₀, hyU⟩
    mem_right := ⟨hzOB, hzU⟩
    left_subset := inter_subset_left.trans hVLA
    left_image := ?_
    right_image := ?_
    right_baseOpen := ?_
    finite := hfin₀.restrictTarget inter_subset_left
    allPieces := allPieces_restrict hpost hV inter_subset_left inter_subset_left hfin₀ hQ₀
  }⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hx.2
  · rintro _ ⟨x, hx, rfl⟩
    exact hx.2.2
  · rintro _ ⟨x, hx, rfl⟩
    exact hx.2

/-- All-pieces certificates can be retained while making every factor
patch used by the product recognition construction genuinely Hausdorff. -/
def finiteProductNeighborhood
    (hpost : ∀ ⦃R S T : PresentedAffinoidAlgebra K⦄
      (r : BoundedAlgHom K S T) (a : BoundedAlgHom K R S) (x : BanachSpectrum T),
      r.toAlgHom.toRingHom.Flat → Function.Surjective r →
      a.toAlgHom.toRingHom.FiniteType →
      Q a (BanachSpectrum.comap r.toBoundedRingHom x) → Q (r.comp a) x)
    {y : A.space} {z : B.space} (hf : f.HasAllPiecesAt Q y)
    (hyz : f.baseMap y = g.baseMap z) :
    FiniteProductNeighborhood Q f g y z :=
  Classical.choice (nonempty_finiteProductNeighborhood hpost hf hyz)

/-- Genuine all-pieces etaleness supplies the joint finite neighborhood,
including the entire pointwise-etale certificate, inside Hausdorff product
patches. No extra property-preservation premise is needed here. -/
def etaleFiniteProductNeighborhood {y : A.space} {z : B.space}
    (hf : f.IsEtaleAtAllPieces y) (hyz : f.baseMap y = g.baseMap z) :
    FiniteProductNeighborhood (fun _ _ a x => a.IsEtaleAtPoint x) f g y z := by
  have hjoint : f.HasAllPiecesAt (fun _ _ a x => a.IsEtaleAtPoint x) y := by
    obtain ⟨W, -, hyW, hW⟩ := hf
    exact hasAllPiecesAt_isEtaleAtPoint_iff.mpr (hW y hyW)
  exact finiteProductNeighborhood
    (fun _ _ _ r a x hr hs hft ha =>
      ⟨(r.isFlatAtPoint_of_flat hr x).comp ha.1,
        BoundedAlgHom.IsUnramifiedAtPoint.comp
          (RingHom.Finite.of_surjective _ hs).finiteType hft
          (r.isUnramifiedAtPoint_of_formallyUnramified
            (RingHom.FormallyUnramified.of_surjective hs) x) ha.2⟩)
    hjoint hyz

namespace FiniteProductNeighborhood

variable {y : A.space} {z : B.space} (N : FiniteProductNeighborhood Q f g y z)

/-- The actual quotient factor patch is Hausdorff. Separation is supplied
by its open subsystem, not by a global separation hypothesis. -/
theorem productPatch_t2 :
    T2Space ↥(FibreProduct.fst f.compatibleRecognitionMap g.compatibleRecognitionMap ⁻¹' N.leftPatch ∩
      FibreProduct.snd f.compatibleRecognitionMap g.compatibleRecognitionMap ⁻¹' N.rightPatch) := by
  let LA : Set f.recognitionSource.space := N.leftPatch
  let RB : Set g.recognitionSource.space := N.rightPatch
  let BC : Set C.fullRecognitionPresentation.space := N.basePatch
  let : T2Space LA := N.leftPatch_t2
  let : T2Space RB := N.rightPatch_t2
  let : T2Space BC := N.basePatch_t2
  have hP : T2Space
      (FibreProduct.patchSystem f.compatibleRecognitionMap g.compatibleRecognitionMap LA RB).Space :=
    FibreProduct.t2Space_patchSystem f.compatibleRecognitionMap g.compatibleRecognitionMap
      N.leftPatch_open N.rightPatch_open f.recognitionSource_hasAllLocalDomains
      g.recognitionSource_hasAllLocalDomains C.fullRecognitionPresentation_hasAllLocalDomains
      N.basePatch_open N.left_image N.right_image
  let : T2Space
      ((FibreProduct.chartSystem f.compatibleRecognitionMap g.compatibleRecognitionMap).subsystem
        (FibreProduct.patchPairs f.compatibleRecognitionMap g.compatibleRecognitionMap LA RB)
        (FibreProduct.isDownwardClosed_patchPairs _ _ LA RB)).Space := hP
  have he : IsOpenEmbedding
      (FibreProduct.patchMap f.compatibleRecognitionMap g.compatibleRecognitionMap LA RB) :=
    FibreProduct.isOpenEmbedding_patchSubsystem
    f.compatibleRecognitionMap g.compatibleRecognitionMap
    f.recognitionSource_hasAllLocalDomains g.recognitionSource_hasAllLocalDomains
    N.leftPatch_open N.rightPatch_open
  have hT : T2Space (range
      (FibreProduct.patchMap f.compatibleRecognitionMap g.compatibleRecognitionMap LA RB)) :=
    he.isEmbedding.toHomeomorph.t2Space
  have hr : range (FibreProduct.patchMap f.compatibleRecognitionMap g.compatibleRecognitionMap LA RB) =
      FibreProduct.fst f.compatibleRecognitionMap g.compatibleRecognitionMap ⁻¹' N.leftPatch ∩
        FibreProduct.snd f.compatibleRecognitionMap g.compatibleRecognitionMap ⁻¹' N.rightPatch :=
    ((FibreProduct.chartSystem f.compatibleRecognitionMap g.compatibleRecognitionMap).range_subsystemMap
      (FibreProduct.patchPairs f.compatibleRecognitionMap g.compatibleRecognitionMap LA RB)
      (FibreProduct.isDownwardClosed_patchPairs _ _ LA RB)).trans
        (FibreProduct.subsystemSupport_patchPairs f.compatibleRecognitionMap g.compatibleRecognitionMap
          f.recognitionSource_hasAllLocalDomains g.recognitionSource_hasAllLocalDomains
          N.leftPatch_open N.rightPatch_open)
  exact hr ▸ hT

/-- Every recognized right affinoid in the chosen right open patch has
a Hausdorff whole finite preimage, before an affinoid parent is supplied. -/
theorem preimage_t2 (R : B.atlas.saturatedAtlas.RecognizedSubset) (hR : R.locus ⊆ N.rightPatch) :
    T2Space ↥(FibreProduct.fst f.compatibleRecognitionMap g.compatibleRecognitionMap ⁻¹' N.leftOpen ∩
      FibreProduct.snd f.compatibleRecognitionMap g.compatibleRecognitionMap ⁻¹' R.locus) := by
  let P := FibreProduct.fst f.compatibleRecognitionMap g.compatibleRecognitionMap ⁻¹' N.leftPatch ∩
    FibreProduct.snd f.compatibleRecognitionMap g.compatibleRecognitionMap ⁻¹' N.rightPatch
  let : T2Space P := N.productPatch_t2
  exact (IsEmbedding.subtypeVal.codRestrict P
    (fun x : ↥(FibreProduct.fst f.compatibleRecognitionMap g.compatibleRecognitionMap ⁻¹' N.leftOpen ∩
      FibreProduct.snd f.compatibleRecognitionMap g.compatibleRecognitionMap ⁻¹' R.locus) =>
        ⟨N.left_subset x.property.1, hR x.property.2⟩)).t2Space

end FiniteProductNeighborhood
end Langlands.Analytic.AffinoidAtlasPresentation.StrongHom
