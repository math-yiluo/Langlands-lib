import Langlands.Geometry.Analytic.CoherentStrongDomainPullback
import Langlands.Geometry.Analytic.StrongAtlasQuasiIsomorphisms
import Langlands.Geometry.Analytic.SaturatedChartCoverRefinement

/-! # Actual direct images of local full domains under full quasi-isomorphisms -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation.StrongHom.IsQuasiIso

open CategoryTheory Set PresentedAffinoidAlgebra IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : AffinoidAtlasPresentation.{u, v, w} K}
  {f : StrongHom A B} (hf : f.IsQuasiIso)

/-- Extend through the actual full representation of the source parent.
The represented algebra is the unchanged local source-domain algebra. -/
def domainImage (U : LocalDomain A.atlas) : LocalDomain B.atlas :=
  ⟨f.chosenTargetIndex U.index,
    (hf.localDomain U.index (f.chosenTargetIndex U.index)
      (f.chosenTarget_admissible U.index)).extend U.domain⟩

@[simp]
theorem domainImage_algebra (U : LocalDomain A.atlas) :
    (hf.domainImage U).algebra = U.algebra := rfl

@[simp]
theorem domainImage_baseMap (U : LocalDomain A.atlas) :
    (hf.domainImage U).domain.baseMap =
      U.domain.baseMap.comp
        (f.pullback U.index (f.chosenTargetIndex U.index)
          (f.chosenTarget_admissible U.index)) := rfl

/-- The actual spectrum realization is the original ambient map after `f`. -/
theorem domainImage_ambientMap (U : LocalDomain A.atlas) (x : BanachSpectrum U.algebra) :
    (hf.domainImage U).ambientMap x = f.baseMap (U.ambientMap x) := by
  exact f.chart_comm U.index (f.chosenTargetIndex U.index)
    (f.chosenTarget_admissible U.index) (U.domain.spectrumMap x)

/-- This is equality of actual ambient subsets, with no chart replacement. -/
theorem domainImage_locus (U : LocalDomain A.atlas) :
    (hf.domainImage U).locus = f.baseMap '' U.locus := by
  rw [← LocalDomain.range_ambientMap, ← U.range_ambientMap, ← Set.range_comp]
  exact congrArg Set.range (funext (hf.domainImage_ambientMap U))

/-- Reexpression over every containing target chart recovers the complete
constructed local pullback, on the unchanged source-domain algebra. -/
theorem domainImage_chartRestriction (U : LocalDomain A.atlas) (j : B.atlas.Index)
    (h : (hf.domainImage U).locus ⊆ Set.range (B.atlas.chart j))
    (hU : f.baseMap '' U.locus ⊆ Set.range (B.atlas.chart j)) :
    B.atlas.domainChartRestriction (hf.domainImage U).index j
        (hf.domainImage U).domain h = f.localChartPullback U j hU := by
  exact B.atlas.domainChartRestriction_eq_changeMapChart
    (hf.domainImage U).index j (hf.domainImage U).domain h

/-- Original full coefficient coherence proves that every source bounded
restriction is also an actual restriction between the image domains. -/
def domainImageMap (hc : f.HasCoherentPullbacks) {U V : LocalDomain A.atlas}
    (p : U ⟶ V) : hf.domainImage U ⟶ hf.domainImage V where
  subset := by
    rw [hf.domainImage_locus, hf.domainImage_locus]
    exact Set.image_mono p.subset
  restriction := p.restriction
  comp_chart j hU hV := by
    have hu : f.baseMap '' U.locus ⊆ Set.range (B.atlas.chart j) := by
      rw [← hf.domainImage_locus U]
      exact hU
    have hv : f.baseMap '' V.locus ⊆ Set.range (B.atlas.chart j) := by
      rw [← hf.domainImage_locus V]
      exact hV
    rw [hf.domainImage_chartRestriction V j hV hv,
      hf.domainImage_chartRestriction U j hU hu]
    exact f.localChartPullback_source hc p j hu hv

@[simp]
theorem domainImageMap_restriction (hc : f.HasCoherentPullbacks)
    {U V : LocalDomain A.atlas} (p : U ⟶ V) :
    (hf.domainImageMap hc p).restriction = p.restriction := rfl

/-- Direct image retains every original quotient algebra and bounded arrow.
No closure, directedness or refinement assumption is required. -/
def domainImageFunctor (hc : f.HasCoherentPullbacks) :
    LocalDomain A.atlas ⥤ LocalDomain B.atlas where
  obj := hf.domainImage
  map := hf.domainImageMap hc
  map_id _ := LocalDomain.Inclusion.ext rfl
  map_comp _ _ := LocalDomain.Inclusion.ext rfl

/-- Ambient injectivity reflects containment of local domains. -/
theorem domainImage_subset_iff (U V : LocalDomain A.atlas) :
    (hf.domainImage U).locus ⊆ (hf.domainImage V).locus ↔ U.locus ⊆ V.locus := by
  rw [hf.domainImage_locus, hf.domainImage_locus]
  constructor
  · intro h x hx
    obtain ⟨y, hy, heq⟩ := h ⟨x, hx, rfl⟩
    exact hf.1.homeomorph.injective heq ▸ hy
  · exact Set.image_mono

/-- Every actual target inclusion has its unique actual source preimage.
Fullness follows from reflected containment; the forward functor still
stores the original full bounded restriction. -/
def fullyFaithfulDomainImageFunctor (hc : f.HasCoherentPullbacks) :
    (hf.domainImageFunctor hc).FullyFaithful where
  preimage {U V} p :=
    LocalDomain.Inclusion.ofSubset U V ((hf.domainImage_subset_iff U V).mp p.subset)
  map_preimage {U V} _ :=
    @Subsingleton.elim (LocalDomain.Inclusion (hf.domainImage U) (hf.domainImage V))
      inferInstance _ _
  preimage_map {U V} _ :=
    @Subsingleton.elim (LocalDomain.Inclusion U V) inferInstance _ _

instance (hc : f.HasCoherentPullbacks) : (hf.domainImageFunctor hc).Full :=
  (hf.fullyFaithfulDomainImageFunctor hc).full

instance (hc : f.HasCoherentPullbacks) : (hf.domainImageFunctor hc).Faithful :=
  (hf.fullyFaithfulDomainImageFunctor hc).faithful

/-- Both object algebras and entire bounded arrows are literally unchanged. -/
theorem domainImageFunctor_comp_toAffinoidSpace (hc : f.HasCoherentPullbacks) :
    hf.domainImageFunctor hc ⋙ LocalDomain.toAffinoidSpace B.atlas =
      LocalDomain.toAffinoidSpace A.atlas := rfl

theorem domainImageFunctor_comp_toTopologicalSpace (hc : f.HasCoherentPullbacks) :
    hf.domainImageFunctor hc ⋙ LocalDomain.toTopologicalSpace B.atlas =
      LocalDomain.toTopologicalSpace A.atlas := rfl

theorem domainImageFunctor_op_comp_boundedPresheaf (hc : f.HasCoherentPullbacks) :
    (hf.domainImageFunctor hc).op ⋙ LocalDomain.boundedPresheaf B.atlas =
      LocalDomain.boundedPresheaf A.atlas := rfl

/-- If the target contains all local domains, choose an original target chart
for the entire actual image, not merely a cover of that image. -/
def imageOriginalChartIndex (hb : B.atlas.HasAllLocalDomains) (U : LocalDomain A.atlas) :
    B.atlas.Index :=
  hb.domainChartIndex (hf.domainImage U).index (hf.domainImage U).domain

theorem range_imageOriginalChartIndex (hb : B.atlas.HasAllLocalDomains)
    (U : LocalDomain A.atlas) :
    Set.range (B.atlas.chart (hf.imageOriginalChartIndex hb U)) =
      f.baseMap '' U.locus :=
  (hb.range_domainChartIndex (hf.domainImage U).index (hf.domainImage U).domain).trans
    (hf.domainImage_locus U)

/-- The actual comparison is over the chosen target parent algebra.
Its maps come from both full domain universal properties. -/
def imageOriginalChartDomainIso (hb : B.atlas.HasAllLocalDomains)
    (U : LocalDomain A.atlas) :
    (hf.domainImage U).domain ≅
      hb.chartDomain (hf.domainImage U).index (hf.domainImage U).domain :=
  hb.chartDomainIso (hf.domainImage U).index (hf.domainImage U).domain

/-- The source-domain quotient algebra is boundedly equivalent to the
original target-chart quotient algebra. -/
def imageOriginalChartBoundedEquiv (hb : B.atlas.HasAllLocalDomains)
    (U : LocalDomain A.atlas) :
    BoundedAlgEquiv K U.algebra (B.atlas.algebra (hf.imageOriginalChartIndex hb U)) :=
  Domain.boundedEquivOfIso (hf.imageOriginalChartDomainIso hb U)

theorem imageOriginalChartBoundedEquiv_comp_baseMap (hb : B.atlas.HasAllLocalDomains)
    (U : LocalDomain A.atlas) :
    (hf.imageOriginalChartBoundedEquiv hb U).toBoundedAlgHom.comp
        (U.domain.baseMap.comp (f.pullback U.index (f.chosenTargetIndex U.index)
          (f.chosenTarget_admissible U.index))) =
      B.atlas.restriction (hf.imageOriginalChartIndex hb U)
        (f.chosenTargetIndex U.index)
        (hb.domainChartIndex_subset (hf.domainImage U).index (hf.domainImage U).domain) :=
  Domain.boundedEquivOfIso_comp_baseMap (hf.imageOriginalChartDomainIso hb U)

end Langlands.Analytic.AffinoidAtlasPresentation.StrongHom.IsQuasiIso
