import Langlands.Geometry.Analytic.AffinoidEtalePieceImage
import Langlands.Geometry.Analytic.EtaleOpenDomains.Proof
import Langlands.Geometry.Analytic.FiniteEtaleOpenChartPullbacks
import Langlands.Geometry.Analytic.FiniteEtaleSourceRecognition
import Langlands.Geometry.Analytic.FullRecognitionIdempotence
import Langlands.Geometry.Analytic.QuasiIsoReverseRecognition
import Langlands.Geometry.Analytic.StrongEtaleSourceOpenLocality

/-! # Recognition of the image of an affinoid piece of an étale chart -/

noncomputable section

universe u

namespace Langlands.Analytic.SpaceAnalytification

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Set
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace
open SaturatedAtlasPresentation AffinoidAtlasPresentation AffinoidAtlasPresentation.StrongHom
open IndexedAffinoidAtlas PresentedAffinoidAlgebra

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

local notation "M" => localizedAffinoidSpectrum (K := K)

private abbrev spectrumMap {R S : PresentedAffinoidAlgebra K} (g : BoundedAlgHom K R S) :
    M S ⟶ M R := SmallAffinoidSpectrum.localizedMapEquiv.{u, u} R S g

private theorem spectrumMap_surjective {R S : PresentedAffinoidAlgebra K}
    (g : BoundedAlgHom K R S)
    (hs : Function.Surjective (BanachSpectrum.comap g.toBoundedRingHom)) :
    Function.Surjective (localizedSpaceFunctor.map (spectrumMap g)) := by
  intro x
  obtain ⟨z, rfl⟩ := (SmallAffinoidSpectrum.spectrumHomeomorph.{u, u} R).surjective x
  obtain ⟨y, hy⟩ := hs z
  exact ⟨SmallAffinoidSpectrum.spectrumHomeomorph.{u, u} S y,
    (SmallAffinoidSpectrum.map_spectrumHomeomorph.{u, u} g y).trans
      (congrArg (SmallAffinoidSpectrum.spectrumHomeomorph.{u, u} R) hy)⟩

section

variable {A B C : AffinoidAtlasPresentation.{u, u, u} K}
  {q : StrongHom A.saturatedPresentation B.saturatedPresentation}
  {f : StrongHom B.saturatedPresentation C.saturatedPresentation} {y : A.space}

/-- The image of the open cover piece intersected with the inverse image of
one recognized target chart, with its actual analytic domain structure. -/
def finiteEtaleImageDomain (N : FiniteEtaleSourceNeighborhoods q f y) (hq : q.IsEtaleAllPieces)
    (W : C.atlas.saturatedAtlas.RecognizedSubset) : (ofFullRecognition B).AnalyticDomain :=
  (ofFullRecognition B).openDomain (q.baseMap '' N.compSource)
    (hq.isOpenMap _ N.isOpen_compSource) ⊓
      domainPreimage f.fullRecognitionLocalizedHom ((ofFullRecognition C).chartDomain W)

set_option backward.isDefEq.respectTransparency false in
theorem finiteEtaleImageDomain_carrier (N : FiniteEtaleSourceNeighborhoods q f y)
    (hq : q.IsEtaleAllPieces) (W : C.atlas.saturatedAtlas.RecognizedSubset) :
    (finiteEtaleImageDomain N hq W).carrier = q.baseMap '' N.compSource ∩ f.baseMap ⁻¹' W.locus := by
  change q.baseMap '' N.compSource ∩ (localizedSpaceFunctor.map f.fullRecognitionLocalizedHom) ⁻¹'
    range W.chart = _
  rw [localizedSpaceFunctor_map_fullRecognition, W.range_chart]
  rfl

set_option maxHeartbeats 1200000 in
set_option backward.isDefEq.respectTransparency false in
/-- Recognize the image by quotienting the piece of the affine test and
identifying its quotient with the actual image domain chart by chart. -/
theorem exists_recognized_finiteEtaleImage [T2Space B.space]
    {X : AlgebraicSpace (Spec (CommRingCat.of K))}
    {p : PointFamily K X (localizationFunctor.obj (ofFullRecognition B))}
    (hp : IsAnalytification K X _ p) (hs : IsSeparated X) (ht : LocallyOfFiniteTypeOverBase X)
    (hq : q.IsEtaleAllPieces) (N : FiniteEtaleSourceNeighborhoods q f y)
    (hPoint : ∀ (R : PresentedAffinoidAlgebra K)
      (r : M R ⟶ localizationFunctor.obj (ofFullRecognition A)),
      ∃ x : RingPoints K X R, affinoidPointHom hp hs ht R x = r ≫ q.fullRecognitionLocalizedHom)
    (W : C.atlas.saturatedAtlas.RecognizedSubset) (hW : W.locus ⊆ N.compTarget) :
    ∃ H : B.atlas.saturatedAtlas.RecognizedSubset,
      H.locus = q.baseMap '' N.compSource ∩ f.baseMap ⁻¹' W.locus := by
  let c := q.saturatedComp f A.atlas.saturatedAtlas_hasAllLocalDomains
    B.atlas.saturatedAtlas_hasAllLocalDomains
  obtain ⟨P, hPW, hP, hg⟩ := N.comp_finiteEtale.2 W hW
  change P.locus = N.compSource ∩ (fun x => f.baseMap (q.baseMap x)) ⁻¹' W.locus at hP
  let g := c.fullRecognitionPairs.pullback P W hPW
  let pInc := (ofFullRecognition A).localizedSmallChart P
  let wInc := (ofFullRecognition C).localizedSmallChart W
  let E := (ofFullRecognition A).openDomain N.compSource N.isOpen_compSource
  let iE := (ofFullRecognition A).localizedDomainInclusion E
  let e := iE ≫ q.fullRecognitionLocalizedHom
  have he : etale e := etale_comp (etaleOpenDomainStatement _ _ _) ((etale_fullRecognition_iff q).mpr hq)
  have hPR : range (localizedSpaceFunctor.map pInc) = P.locus :=
    ((ofFullRecognition A).localizedSmallChart_range P).trans P.range_chart
  obtain ⟨r, hr⟩ := exists_localizedDomainLift E pInc (fun z => by
    have hz : localizedSpaceFunctor.map pInc z ∈ P.locus := hPR ▸ mem_range_self z
    rw [hP] at hz
    exact hz.1)
  have hr' : r ≫ e = pInc ≫ q.fullRecognitionLocalizedHom :=
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ q.fullRecognitionLocalizedHom) hr)
  have hC : pInc ≫ c.fullRecognitionLocalizedHom = spectrumMap g ≫ wInc :=
    localizedSmallChart_comp_fullRecognition c P W hPW
  have hpre : range ((ofFullRecognition A).presentation.atlas.chart P) = E.carrier ∩
      (localizedSpaceFunctor.map c.fullRecognitionLocalizedHom) ⁻¹'
        range ((ofFullRecognition C).presentation.atlas.chart W) := by
    change range P.chart = N.compSource ∩
      (localizedSpaceFunctor.map c.fullRecognitionLocalizedHom) ⁻¹' range W.chart
    rw [localizedSpaceFunctor_map_fullRecognition, P.range_chart, W.range_chart]
    exact hP
  have hPull : IsPullback r (spectrumMap g) (e ≫ f.fullRecognitionLocalizedHom) wInc := by
    change IsPullback r (spectrumMap g)
      ((iE ≫ q.fullRecognitionLocalizedHom) ≫ f.fullRecognitionLocalizedHom) wInc
    rw [Category.assoc, fullRecognition_comp]
    exact isPullback_localizedSmallChart_of_domainPreimage
      (A := ofFullRecognition A) (B := ofFullRecognition C) E P W c.fullRecognitionLocalizedHom
      r (spectrumMap g) hr hC hpre
  obtain ⟨x, hx⟩ := hPoint P.algebra pInc
  let a := affinoidPointHom hp hs ht P.algebra x
  let Q : AffinoidEtalePieceQuotient a := affinoidEtalePieceQuotient hp hs ht x g hg.1 hg.2
    e he r (hr'.trans hx.symm) f.fullRecognitionLocalizedHom wInc hPull
  let D := finiteEtaleImageDomain N hq W
  have hD : D.carrier = q.baseMap '' N.compSource ∩ f.baseMap ⁻¹' W.locus :=
    finiteEtaleImageDomain_carrier N hq W
  have hRange : range (localizedSpaceFunctor.map a) = D.carrier := by
    change range (localizedSpaceFunctor.map (affinoidPointHom hp hs ht P.algebra x)) = D.carrier
    rw [hx, localizedSpaceFunctor.map_comp, localizedSpaceFunctor_map_fullRecognition]
    change range (q.baseMap ∘ localizedSpaceFunctor.map pInc) = D.carrier
    rw [range_comp, hPR, hP, hD]
    ext b
    constructor
    · rintro ⟨z, ⟨hz, hWz⟩, rfl⟩
      exact ⟨⟨z, hz, rfl⟩, hWz⟩
    · rintro ⟨⟨z, hz, rfl⟩, hWz⟩
      exact ⟨z, ⟨hz, hWz⟩, rfl⟩
  have hSurj := spectrumMap_surjective Q.coverMap Q.cover_surjective
  have hImage : range (localizedSpaceFunctor.map Q.map) = D.carrier := by
    calc
      _ = range ((localizedSpaceFunctor.map Q.map) ∘
          (localizedSpaceFunctor.map (spectrumMap Q.coverMap))) :=
        (hSurj.range_comp (localizedSpaceFunctor.map Q.map)).symm
      _ = range (localizedSpaceFunctor.map (spectrumMap Q.coverMap ≫ Q.map)) := by
        rw [localizedSpaceFunctor.map_comp]
        rfl
      _ = D.carrier := (congrArg
        (fun m : M P.algebra ⟶ localizationFunctor.obj (ofFullRecognition B) =>
          range (localizedSpaceFunctor.map m)) Q.cover_comp_map).trans hRange
  obtain ⟨j, hj⟩ := exists_localizedDomainLift D Q.map (fun z => hImage ▸ mem_range_self z)
  let iD := (ofFullRecognition B).localizedDomainInclusion D
  have hCovers (k : ((ofFullRecognition B).domain D).presentation.atlas.Index) :
      ∃ (S : PresentedAffinoidAlgebra K)
        (gJ : BoundedAlgHom K (((ofFullRecognition B).domain D).presentation.atlas.algebra k) S)
        (rJ : M S ⟶ M P.algebra),
        gJ.IsFiniteBanach ∧ gJ.AlgebraicallyFiniteEtale ∧
          Function.Surjective (BanachSpectrum.comap gJ.toBoundedRingHom) ∧
          rJ ≫ a = spectrumMap gJ ≫ ((ofFullRecognition B).domain D).localizedSmallChart k ≫ iD := by
    let J : B.atlas.saturatedAtlas.RecognizedSubset := k.val
    have hJD : J.locus ⊆ D.carrier := J.range_chart ▸ k.property
    have hJH : J.locus ⊆ q.baseMap '' N.compSource ∩ f.baseMap ⁻¹' W.locus := hD ▸ hJD
    have hJU : J.locus ⊆ N.coverTarget := by
      intro z hz
      obtain ⟨v, hv, rfl⟩ := (hJH hz).1
      exact N.cover_finiteEtale.1 ⟨v, N.compSource_subset hv, rfl⟩
    have hcut : N.compSource ∩ q.baseMap ⁻¹' J.locus = P.locus ∩ q.baseMap ⁻¹' J.locus := by
      rw [hP]
      exact Set.ext fun v => ⟨fun ⟨hv, hJv⟩ => ⟨⟨hv, (hJH hJv).2⟩, hJv⟩,
        fun ⟨⟨hv, _⟩, hJv⟩ => ⟨hv, hJv⟩⟩
    obtain ⟨R, hRP, hRJ, hfin, het, hsurj⟩ := N.cover_finiteEtale.exists_chartCover_of_openCut
      N.isOpen_compSource N.compSource_subset P J hJU (fun _ h => (hJH h).1) hcut
    let gJ := q.fullRecognitionPairs.pullback R J hRJ
    let rJ := spectrumMap (R.restriction P hRP)
    refine ⟨R.algebra, gJ, rJ, hfin, het, hsurj, ?_⟩
    calc
      rJ ≫ a = (rJ ≫ pInc) ≫ q.fullRecognitionLocalizedHom := by rw [Category.assoc]; exact congrArg (rJ ≫ ·) hx
      _ = (ofFullRecognition A).localizedSmallChart R ≫ q.fullRecognitionLocalizedHom :=
        congrArg (· ≫ q.fullRecognitionLocalizedHom) (localizedSmallChart_restriction R P hRP)
      _ = spectrumMap gJ ≫ (ofFullRecognition B).localizedSmallChart J :=
        localizedSmallChart_comp_fullRecognition q R J hRJ
      _ = _ := congrArg (spectrumMap gJ ≫ ·) (localizedSmallChart_domain_comp (ofFullRecognition B) D k).symm
  let eD := Q.isoOfFiniteChartCovers ((ofFullRecognition B).domain D) iD j hj hCovers
  obtain ⟨V, hV⟩ := exists_recognized_locus_of_affinoid_iso D Q.algebra eD.symm
  exact ⟨B.atlas.fullRecognitionIdempotenceIndex V,
    (B.atlas.fullRecognitionIdempotenceIndex_locus V).trans (hV.trans hD)⟩

end

end Langlands.Analytic.SpaceAnalytification
