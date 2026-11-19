import Langlands.Geometry.Analytic.SmallFiniteProductNeighborhoods
import Langlands.Geometry.Analytic.FullRecognitionIdempotence
import Langlands.Geometry.Analytic.SubatlasReverseRecognition
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteBanachPushout.Proof
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteTensorComparison.Proof

/-! # The common structure map of two étale factors -/

noncomputable section

universe u v

namespace Langlands.Analytic.AffinoidAtlasPresentation.StrongHom

open CategoryTheory Set Topology PresentedAffinoidAlgebra IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : AffinoidAtlasPresentation.{u, v, v} K}
  (f : StrongHom A.saturatedPresentation C.saturatedPresentation)
  (g : StrongHom B.saturatedPresentation C.saturatedPresentation)
  [Small.{v} (FibreProduct.chartSystem f.compatibleRecognitionMap g.compatibleRecognitionMap).Space]

/-- The complete common structure map to the recognized base, through
one of the canonical small product projections. -/
abbrev recognitionSmallCommon : StrongHom (recognitionSmallProductPresentation f g).saturatedPresentation
    C.fullRecognitionPresentation.saturatedPresentation :=
  (recognitionSmallSnd f g).saturationExtension.saturatedComp
    g.compatibleRecognitionMap.saturationExtension
    (recognitionSmallProductPresentation f g).atlas.saturatedAtlas_hasAllLocalDomains
    g.recognitionSource.atlas.saturatedAtlas_hasAllLocalDomains

private theorem finite_of_recognized_eq
    {B₁ C₁ : AffinoidAtlasPresentation.{u, v, v} K}
    (F : StrongHom B₁.saturatedPresentation C₁.saturatedPresentation)
    {R R' : B₁.atlas.saturatedAtlas.RecognizedSubset}
    (h : R = R') (W : C₁.atlas.saturatedAtlas.RecognizedSubset)
    (hR : F.baseMap '' range R.chart ⊆ range W.chart)
    (hR' : F.baseMap '' range R'.chart ⊆ range W.chart)
    (hfin : (F.fullRecognitionPairs.pullback R' W hR').IsFiniteBanach) :
    (F.fullRecognitionPairs.pullback R W hR).IsFiniteBanach := by
  subst R'
  exact hfin

set_option maxHeartbeats 1600000 in
private theorem recognitionSmallCommon_hasAllEtalePieces
    (hf : f.IsEtaleAllPieces) (hg : g.compatibleRecognitionMap.saturationExtension.IsEtaleAllPieces)
    (t : (recognitionSmallProductPresentation f g).space) :
    (recognitionSmallCommon f g).HasAllPiecesAt (fun _ _ a x => a.IsEtaleAtPoint x) t := by
  classical
  let D₀ := recognitionSmallProductPresentation f g
  let B₀ := g.recognitionSource
  let C₀ := C.fullRecognitionPresentation
  let F := f.compatibleRecognitionMap.saturationExtension
  let G := g.compatibleRecognitionMap.saturationExtension
  let r := (recognitionSmallSnd f g).saturationExtension
  let m := recognitionSmallCommon f g
  let left := FibreProduct.smallFstBase f.compatibleRecognitionMap g.compatibleRecognitionMap
    f.recognitionSource_hasAllLocalDomains g.recognitionSource_hasAllLocalDomains
    C.fullRecognitionPresentation_hasAllLocalDomains
  let right := (recognitionSmallSnd f g).baseMap
  let y := left t
  let z := right t
  have hbase (a : D₀.space) : f.baseMap (left a) = g.baseMap (right a) :=
    FibreProduct.baseMap_fst f.compatibleRecognitionMap g.compatibleRecognitionMap
      ((recognitionProductShrink f g).symm a)
  have hbase' (a : D₀.space) : F.baseMap (left a) = G.baseMap (right a) := hbase a
  have hmy : m.baseMap t = f.baseMap y := (hbase t).symm
  have hmz : m.baseMap t = G.baseMap z := rfl
  let N := etaleFiniteProductNeighborhood (f := f) (g := g) (hf y) (hbase t)
  let M := etaleFiniteProductNeighborhood (f := G) (g := F) (hg z) (hbase' t).symm
  have hindex : Nonempty (FibreProduct.LocalAtlasIndex f.compatibleRecognitionMap g.compatibleRecognitionMap) := by
    obtain ⟨i, -⟩ := D₀.atlas.exists_mem_range_chart t
    exact ⟨(equivShrink (FibreProduct.LocalAtlasIndex f.compatibleRecognitionMap g.compatibleRecognitionMap)).symm i⟩
  let : Nonempty (FibreProduct.LocalAtlasIndex f.compatibleRecognitionMap g.compatibleRecognitionMap) := hindex
  let : T2Space N.leftPatch := N.leftPatch_t2
  let OB : Set B.space := M.leftPatch
  let : T2Space OB := M.leftPatch_t2
  have hOB : IsOpen OB := M.leftPatch_open
  let V := left ⁻¹' N.leftOpen ∩ right ⁻¹' M.leftOpen
  let U := N.baseOpen ∩ M.baseOpen
  have hVU : m.baseMap '' V ⊆ U := by
    rintro _ ⟨a, ha, rfl⟩
    refine ⟨?_, M.finite.1 ⟨right a, ha.2, rfl⟩⟩
    change g.baseMap (right a) ∈ N.baseOpen
    exact hbase a ▸ N.finite.1 ⟨left a, ha.1, rfl⟩
  have hpieces (W₀ : C₀.atlas.saturatedAtlas.RecognizedSubset) (hW₀ : W₀.locus ⊆ U) :
      ∃ (P : D₀.atlas.saturatedAtlas.RecognizedSubset)
        (hPW : m.baseMap '' range P.chart ⊆ range W₀.chart),
          P.locus = V ∩ m.baseMap ⁻¹' W₀.locus ∧
          (m.fullRecognitionPairs.pullback P W₀ hPW).IsFiniteBanach ∧
          (m.baseMap t ∈ W₀.locus → ∀ s : BanachSpectrum P.algebra, P.chart s = t →
            (m.fullRecognitionPairs.pullback P W₀ hPW).IsEtaleAtPoint s) := by
    have hWL : W₀.locus ⊆ N.baseOpen := hW₀.trans inter_subset_left
    have hWR : W₀.locus ⊆ M.baseOpen := hW₀.trans inter_subset_right
    let W := C.atlas.fullRecognitionIdempotenceIndex W₀
    have hW : W.locus = W₀.locus := rfl
    obtain ⟨R₀, hR₀W₀, hR₀, hR₀fin⟩ := M.finite.2 W₀ hWR
    let R₁ := B.fullRecognitionPresentation.atlas.subatlasReverseRecognizedSubset
      g.recognitionSourceSelection_locallyRefining R₀
    let R := B.atlas.fullRecognitionIdempotenceIndex R₁
    have hR : R.locus = R₀.locus :=
      B.fullRecognitionPresentation.atlas.subatlasReverseRecognizedSubset_locus
        g.recognitionSourceSelection_locallyRefining R₀
    have hRW : g.baseMap '' R.locus ⊆ W.locus := by
      rintro _ ⟨a, ha, rfl⟩
      have ha₀ : a ∈ R₀.locus := hR ▸ ha
      have haW : G.baseMap a ∈ W₀.locus := (hR₀ ▸ ha₀).2
      exact hW.symm ▸ haW
    have hWsub : W.locus ⊆ N.baseOpen := hW.symm ▸ hWL
    let D := singleFiniteProductPiece N.finite R W hWsub hRW
    have hRpatch : R.locus ⊆ OB := by
      rw [hR, hR₀]
      exact inter_subset_left.trans M.left_subset
    let P := D.smallRecognizedPreimage N.leftPatch OB N.leftPatch_open hOB
      N.left_subset hRpatch
    let H := D.targetRecognition
    have hH : H = R₀ := Subtype.ext (Subtype.ext (D.targetRecognition_locus.trans hR))
    have hHW : G.baseMap '' range H.chart ⊆ range W₀.chart := hH.symm ▸ hR₀W₀
    have hHpre : H.locus = M.leftOpen ∩ G.baseMap ⁻¹' W₀.locus := hH.symm ▸ hR₀
    have hHfin : (G.fullRecognitionPairs.pullback H W₀ hHW).IsFiniteBanach :=
      finite_of_recognized_eq G hH W₀ hHW hR₀W₀ hR₀fin
    have hPH : r.baseMap '' range P.chart ⊆ range H.chart :=
      FibreProduct.smallGoodPair_recognized_admissible f.compatibleRecognitionMap g.compatibleRecognitionMap
        f.recognitionSource_hasAllLocalDomains g.recognitionSource_hasAllLocalDomains
        C.fullRecognitionPresentation_hasAllLocalDomains D.pairIndex
        (D.pairIndex_good N.leftPatch OB N.leftPatch_open hOB
          N.left_subset hRpatch)
    have hPW : m.baseMap '' range P.chart ⊆ range W₀.chart := by
      rintro _ ⟨a, ha, rfl⟩
      exact hHW ⟨r.baseMap a, hPH ⟨a, ha, rfl⟩, rfl⟩
    let r₀ := r.fullRecognitionPairs.pullback P H hPH
    let g₀ := G.fullRecognitionPairs.pullback H W₀ hHW
    have hmaps : m.fullRecognitionPairs.pullback P W₀ hPW = r₀.comp g₀ :=
      fullRecognitionPairs_comp r G P H W₀ hPH hHW hPW
    have hrfin : r₀.IsFiniteBanach :=
      D.actualPullback_isFiniteBanach N.leftPatch OB N.leftPatch_open hOB
        N.left_subset hRpatch AffinoidPushout.finiteBanachPushout
    have hPlocus : P.locus = V ∩ m.baseMap ⁻¹' W₀.locus := by
      refine (D.smallRecognizedPreimage_locus N.leftPatch OB N.leftPatch_open
        hOB N.left_subset hRpatch).trans ?_
      change left ⁻¹' N.leftOpen ∩ right ⁻¹' R.locus = V ∩ m.baseMap ⁻¹' W₀.locus
      have hRpre : R.locus = M.leftOpen ∩ G.baseMap ⁻¹' W₀.locus :=
        D.targetRecognition_locus.symm.trans hHpre
      ext a
      change left a ∈ N.leftOpen ∧ right a ∈ R.locus ↔
        (left a ∈ N.leftOpen ∧ right a ∈ M.leftOpen) ∧ G.baseMap (right a) ∈ W₀.locus
      rw [hRpre]
      exact and_assoc.symm
    refine ⟨P, hPW, hPlocus, hmaps ▸ hrfin.comp hHfin, ?_⟩
    intro ht s hs
    have hty : f.baseMap y ∈ W.locus := hW.symm ▸ (hmy ▸ ht)
    have htz : G.baseMap z ∈ W₀.locus := hmz ▸ ht
    have hret : r₀.IsEtaleAtPoint s :=
      D.actualPullback_isEtaleAtPoint_of_first_image N.leftPatch OB N.leftPatch_open
        hOB N.left_subset hRpatch AffinoidPushout.finiteBanachPushout
        AffinoidPushout.finiteTensorComparison y
        (N.allPieces W hWsub hty D.left D.left_admissible D.left_locus) s
        (congrArg left hs)
    have hz' : H.chart (BanachSpectrum.comap r₀.toBoundedRingHom s) = z :=
      (r.fullRecognitionPairs.chart_comm P H hPH s).trans (congrArg r.baseMap hs)
    have hget := M.allPieces W₀ hWR htz H hHW hHpre _ hz'
    exact hmaps ▸ hret.comp hrfin.finite.finiteType hHfin.finite.finiteType hget
  refine ⟨V, U, (N.leftOpen_open.preimage left.continuous).inter
      (M.leftOpen_open.preimage right.continuous), N.baseOpen_open.inter M.baseOpen_open,
    ⟨N.mem_left, M.mem_left⟩, ⟨hVU, ?_⟩, ?_⟩
  · intro W hW
    obtain ⟨P, hp, hP, hfin, -⟩ := hpieces W hW
    exact ⟨P, hp, hP, hfin⟩
  · intro W hW hWt P hp hP s hs
    obtain ⟨P₀, hp₀, hP₀, -, hQ⟩ := hpieces W hW
    have he : P = P₀ := Subtype.ext (Subtype.ext (hP.trans hP₀.symm))
    subst P
    exact hQ hWt s hs

set_option linter.defProp false in
/-- For two étale maps to one base the actual common product map is étale
on every recognized piece of that base. -/
def recognitionSmallCommon_isEtaleAllPieces
    (hf : f.IsEtaleAllPieces) (hg : g.compatibleRecognitionMap.saturationExtension.IsEtaleAllPieces) :
    (recognitionSmallCommon f g).IsEtaleAllPieces := by
  intro t
  exact ⟨univ, isOpen_univ, mem_univ t, fun x _ => hasAllPiecesAt_isEtaleAtPoint_iff.mp
    (recognitionSmallCommon_hasAllEtalePieces f g hf hg x)⟩

end Langlands.Analytic.AffinoidAtlasPresentation.StrongHom
