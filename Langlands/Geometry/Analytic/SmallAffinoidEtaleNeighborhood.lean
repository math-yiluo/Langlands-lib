import Langlands.Geometry.Analytic.SmallAffinoidEtaleBaseChange
import Langlands.Geometry.Analytic.AffinoidEtaleLocus
import Langlands.Geometry.Analytic.EtaleOpenDomains.Proof
import Langlands.Geometry.Analytic.LocalizedEtaleComposition

/-! # The actual open étale part of a finite small affinoid map -/

noncomputable section

universe u v w

namespace Langlands.Analytic.SmallAffinoidSpectrum

open CategoryTheory Set PresentedAffinoidAlgebra AffinoidAtlasPresentation Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

private theorem originalChart_heq {X : Type v} [TopologicalSpace X]
    (a : IndexedAffinoidAtlas.{u, v, w} K X) (i : a.Index) :
    HEq (a.saturatedAtlas.chart (a.originalSaturatedIndex i)) (a.chart i) := by
  have key : ∀ U : IndexedAffinoidAtlas.LocalDomain a, U = a.originalLocalDomain i →
      HEq (U.ambientMap : BanachSpectrum U.algebra → X) (a.chart i) := by
    intro U hU
    subst U
    exact heq_of_eq (funext (a.originalLocalDomain_ambientMap i))
  exact key _ (a.saturatedRepresentative_original i)

theorem canonicalGlobalChart_chart_heq (S : PresentedAffinoidAlgebra K)
    [Small.{v} (BanachSpectrum S)] :
    HEq ((saturated S).presentation.atlas.saturatedAtlas.chart (canonicalGlobalChart S))
      (spectrumHomeomorph S : BanachSpectrum S → (saturated S).presentation.space) :=
  (originalChart_heq (saturated S).presentation.atlas (globalChart S)).trans
    (originalChart_heq (presentation S).atlas PUnit.unit)

variable {R S : PresentedAffinoidAlgebra K}
    [Small.{v} (BanachSpectrum R)] [Small.{v} (BanachSpectrum S)]
    (f : BoundedAlgHom K R S)

omit [CompleteSpace K] [Small.{v} (BanachSpectrum R)] [Small.{v} (BanachSpectrum S)] in
private theorem finite_of_heq {R' S' : PresentedAffinoidAlgebra K}
    (hR : R' = R) (hS : S' = S) {f' : BoundedAlgHom K R' S'} (he : HEq f' f)
    (hf : f.IsFiniteBanach) : f'.IsFiniteBanach := by
  cases hR
  cases hS
  cases eq_of_heq he
  exact hf

omit [CompleteSpace K] [Small.{v} (BanachSpectrum R)] [Small.{v} (BanachSpectrum S)] in
private theorem exists_point_of_heq {R' S' : PresentedAffinoidAlgebra K} {X : Type v}
    (hR : R' = R) (hS : S' = S) {f' : BoundedAlgHom K R' S'}
    (c' : BanachSpectrum S' → X) (c : BanachSpectrum S → X)
    (he : HEq f' f) (hc : HEq c' c) (x : BanachSpectrum S) (hx : f.IsEtaleAtPoint x) :
    ∃ t : BanachSpectrum S', c' t = c x ∧ f'.IsEtaleAtPoint t := by
  cases hR
  cases hS
  cases eq_of_heq he
  cases eq_of_heq hc
  exact ⟨x, rfl, hx⟩

/-- Pointwise étaleness at a single original point implies all-pieces
étaleness at its corresponding point of the canonical extension. -/
theorem canonicalMap_isEtaleAtAllPieces_of_pointwise
    (hpush : AffinoidPushout.FiniteBanachPushoutStatement K)
    (htensor : AffinoidPushout.FiniteTensorComparisonStatement K)
    (hf : f.IsFiniteBanach) (x : BanachSpectrum S) (hx : f.IsEtaleAtPoint x) :
    (canonicalMap f).IsEtaleAtAllPieces (spectrumHomeomorph S x) := by
  let i := canonicalGlobalChart S
  let j := canonicalGlobalChart R
  let hij := canonicalGlobalChart_admissible f
  let φ := (canonicalMap f).pullback i j hij
  let c := (saturated S).presentation.atlas.saturatedAtlas.chart i
  have hφ : φ.IsFiniteBanach := finite_of_heq f
    (canonicalGlobalChart_algebra R) (canonicalGlobalChart_algebra S)
    (canonicalMap_pullback_global_heq f) hf
  obtain ⟨t, htx, ht⟩ := exists_point_of_heq f
    (canonicalGlobalChart_algebra R) (canonicalGlobalChart_algebra S)
    c (spectrumHomeomorph S) (canonicalMap_pullback_global_heq f)
    (canonicalGlobalChart_chart_heq S) x hx
  have hc : IsHomeomorph c := isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨(saturated S).presentation.atlas.saturatedAtlas.isEmbedding_chart i,
      fun z => (canonicalGlobalChart_range S).symm.subset (mem_univ z)⟩
  apply (canonicalMap f).isEtaleAtAllPieces_of_globalCharts i j hij hpush htensor
    (canonicalGlobalChart_range S) (canonicalGlobalChart_range R) hφ
    (c '' φ.pointwiseEtaleLocus) (hc.isOpenMap _ (φ.isOpen_pointwiseEtaleLocus hφ.finite.finiteType))
  · intro t' ht'
    obtain ⟨t'', ht'', htt⟩ := ht'
    exact hc.injective htt ▸ ht''
  · exact ⟨t, ht, htx⟩

/-- The open ordinary étale locus in the actual small source space. -/
def etaleOpenSet : Set (saturated S).presentation.space :=
  spectrumHomeomorph S '' f.pointwiseEtaleLocus

omit [Small.{v} (BanachSpectrum R)] in
theorem isOpen_etaleOpenSet (hf : f.IsFiniteBanach) : IsOpen (etaleOpenSet f) :=
  (spectrumHomeomorph S).isOpenMap _ (f.isOpen_pointwiseEtaleLocus hf.finite.finiteType)

/-- The actual analytic space of the open étale locus of a finite map. -/
def etaleOpenSpace (hf : f.IsFiniteBanach) : SaturatedAtlasPresentation.{u, v, v} K :=
  (saturated S).domain ((saturated S).openDomain (etaleOpenSet f) (isOpen_etaleOpenSet f hf))

/-- The unchanged map restricted to its actual open étale source locus. -/
def etaleOpenMap (hf : f.IsFiniteBanach) : etaleOpenSpace f hf ⟶ saturated R :=
  (saturated S).domainInclusion
    ((saturated S).openDomain (etaleOpenSet f) (isOpen_etaleOpenSet f hf)) ≫ map f

/-- The restricted map is étale for the actual localized analytic category. -/
theorem etaleOpenMap_etale
    (hpush : AffinoidPushout.FiniteBanachPushoutStatement K)
    (htensor : AffinoidPushout.FiniteTensorComparisonStatement K)
    (hf : f.IsFiniteBanach) :
    SaturatedAtlasPresentation.etale
      (SaturatedAtlasPresentation.localizationFunctor.map (etaleOpenMap f hf)) := by
  let D := (saturated S).openDomain (etaleOpenSet f) (isOpen_etaleOpenSet f hf)
  let j := (saturated S).domainInclusion D
  have hj : SaturatedAtlasPresentation.strongEtale j :=
    (SaturatedAtlasPresentation.etale_localizationFunctor_map_iff_strongEtale j).mp
      (SaturatedAtlasPresentation.etaleOpenDomainStatement
        (SaturatedAtlasPresentation.localizationFunctor.obj (saturated S))
        (etaleOpenSet f) (isOpen_etaleOpenSet f hf))
  apply SaturatedAtlasPresentation.etale_map_of_strongEtale
  change SaturatedAtlasPresentation.strongEtale (j ≫ map f)
  unfold SaturatedAtlasPresentation.strongEtale at hj ⊢
  rw [Functor.map_comp]
  intro t
  have ht : ((SaturatedAtlasPresentation.compatibleFunctor ⋙
      CompatibleAtlasPresentation.saturationFunctor).map j).baseMap t ∈ etaleOpenSet f :=
    t.property
  obtain ⟨s, hs, hst⟩ := ht
  exact (hj t).comp (hst ▸ canonicalMap_isEtaleAtAllPieces_of_pointwise f hpush htensor hf s hs)

end Langlands.Analytic.SmallAffinoidSpectrum
