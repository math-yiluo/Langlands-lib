import Langlands.Geometry.Analytic.SaturatedStrongLocalization
import Langlands.Geometry.Analytic.OriginalDomainStrongRestriction
import Langlands.Geometry.Analytic.SaturatedAtlasDomainClosure

/-! # Analytic domains of saturated presentations as analytic spaces -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open CategoryTheory

namespace IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] {a : IndexedAffinoidAtlas.{u, v, w} K X}

/-- The atlas of charts contained in a domain keeps all local domains: a local domain of a
contained chart is a chart of the ambient atlas, and it is contained in the domain. -/
theorem HasAllLocalDomains.subspaceAtlas (ha : a.HasAllLocalDomains) (S : Set X)
    (hS : a.IsOriginalChartDomain S) : (a.subspaceAtlas S hS).HasAllLocalDomains := by
  refine Set.Subset.antisymm ?_ (a.subspaceAtlas S hS).chartFamily_subset_localDomainFamily
  rintro _ ⟨U, rfl⟩
  obtain ⟨j, hj⟩ := ha.exists_chart ⟨U.index.val, U.domain⟩
  simp only [LocalDomain.locus] at hj
  have hjS : Set.range (a.chart j) ⊆ S := by
    rw [hj]
    rintro _ ⟨x, -, rfl⟩
    exact U.index.property ⟨x, rfl⟩
  let c : a.SubspaceChart S := ⟨j, hjS⟩
  refine ⟨c, ?_⟩
  change Set.range (a.subspaceChart S c) = a.subspaceChart S U.index '' U.domain.locus
  rw [a.range_subspaceChart]
  ext y
  constructor
  · intro hy
    rw [Set.mem_preimage, hj] at hy
    obtain ⟨x, hx, hxy⟩ := hy
    exact ⟨x, hx, Subtype.ext hxy⟩
  · rintro ⟨x, hx, rfl⟩
    change a.chart U.index.val x ∈ Set.range (a.chart j)
    rw [hj]
    exact ⟨x, hx, rfl⟩

end IndexedAffinoidAtlas

namespace SaturatedAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (S : SaturatedAtlasPresentation.{u, v, w} K)

/-- Analytic domains of the space of `S`: subsets in which the charts contained in them form
a quasinet in the induced topology. -/
abbrev AnalyticDomain := S.presentation.atlas.OriginalChartDomain

/-- The analytic domain `D` with the atlas of the charts of `S` contained in it, as a saturated
presentation. -/
def domain (D : S.AnalyticDomain) : SaturatedAtlasPresentation.{u, v, w} K where
  presentation := S.presentation.originalDomainPresentation D
  hasAllLocalDomains := S.hasAllLocalDomains.subspaceAtlas D.carrier D.is_domain

@[simp]
theorem domain_space (D : S.AnalyticDomain) :
    ((S.domain D).presentation.space : Type v) = D.carrier := rfl

/-- The canonical morphism `ν : D → X` of an analytic domain: the inclusion of the subspace,
with the original bounded restrictions as pieces. -/
def domainInclusion (D : S.AnalyticDomain) : S.domain D ⟶ S :=
  S.presentation.subspaceStrongInclusion D.carrier D.is_domain

@[simp]
theorem domainInclusion_baseMap (D : S.AnalyticDomain) (x : D.carrier) :
    (S.domainInclusion D).baseMap x = x.val := rfl

theorem range_domainInclusion_baseMap (D : S.AnalyticDomain) :
    Set.range (S.domainInclusion D).baseMap = D.carrier := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact y.property
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

theorem injective_domainInclusion_baseMap (D : S.AnalyticDomain) :
    Function.Injective (S.domainInclusion D).baseMap :=
  Subtype.val_injective

/-- The strong inclusion of nested analytic domains. -/
def domainMap {D E : S.AnalyticDomain} (h : D ≤ E) : S.domain D ⟶ S.domain E :=
  S.presentation.originalDomainStrongMap h

@[simp]
theorem domainMap_baseMap_val {D E : S.AnalyticDomain} (h : D ≤ E) (x : D.carrier) :
    ((S.domainMap h).baseMap x).val = x.val := rfl

/-- The affinoid domain given by a chart of `S`. -/
def chartDomain (i : S.presentation.atlas.Index) : S.AnalyticDomain :=
  IndexedAffinoidAtlas.OriginalChartDomain.ofChart i

@[simp]
theorem chartDomain_carrier (i : S.presentation.atlas.Index) :
    (S.chartDomain i).carrier = Set.range (S.presentation.atlas.chart i) := rfl

/-- Compact analytic domains: the subset is compact and Hausdorff (Berkovich's compact spaces
are Hausdorff). -/
def IsCompactDomain (D : S.AnalyticDomain) : Prop :=
  IsCompact D.carrier ∧ T2Space D.carrier

/-- Affinoid domains given by charts are compact: the chart range is homeomorphic to the
compact Hausdorff Banach spectrum. -/
theorem isCompactDomain_chartDomain (i : S.presentation.atlas.Index) :
    S.IsCompactDomain (S.chartDomain i) :=
  ⟨isCompact_range (S.presentation.atlas.isEmbedding_chart i).continuous,
    (S.presentation.atlas.isEmbedding_chart i).toHomeomorph.t2Space⟩

/-- In a Hausdorff space, a domain that is a finite union of chart ranges is compact. -/
theorem isCompactDomain_of_eq_iUnion [T2Space S.presentation.space] {ι : Type*} [Finite ι]
    (D : S.AnalyticDomain) (V : ι → S.presentation.atlas.Index)
    (hD : D.carrier = ⋃ k, Set.range (S.presentation.atlas.chart (V k))) :
    S.IsCompactDomain D := by
  refine ⟨?_, inferInstance⟩
  rw [hD]
  exact isCompact_iUnion fun k => (S.isCompactDomain_chartDomain (V k)).1

/-- The image in the localized category of the canonical morphism of an analytic domain. -/
def localizedDomainInclusion (D : S.AnalyticDomain) :
    localizationFunctor.obj (S.domain D) ⟶ localizationFunctor.obj S :=
  localizationFunctor.map (S.domainInclusion D)

/-- Its underlying continuous map is the inclusion of the subspace. -/
theorem localizedSpaceFunctor_map_localizedDomainInclusion (D : S.AnalyticDomain)
    (x : D.carrier) :
    localizedSpaceFunctor.map (S.localizedDomainInclusion D) x = x.val := by
  change (localizationFunctor ⋙ localizedSpaceFunctor).map (S.domainInclusion D) x = x.val
  rw [Functor.congr_hom (localizationFunctor_localizedSpaceFunctor (K := K))
    (S.domainInclusion D)]
  rfl

variable {S} in
/-- A morphism of analytic spaces identifies its source with an affinoid domain of its target:
up to an isomorphism of the source, it is the canonical morphism of the affinoid domain of a
chart of the target's presentation. -/
def IsAffinoidDomainEmbedding {V W : LocalizedCategory.{u, v, w} (K := K)} (j : V ⟶ W) :
    Prop :=
  ∃ (i : (localizedObjectEquiv.symm W).presentation.atlas.Index)
    (e : V ≅ localizationFunctor.obj
      ((localizedObjectEquiv.symm W).domain ((localizedObjectEquiv.symm W).chartDomain i))),
    j = e.hom ≫ (localizedObjectEquiv.symm W).localizedDomainInclusion _

/-- The canonical morphism of the affinoid domain of a chart is an affinoid domain
embedding. -/
theorem isAffinoidDomainEmbedding_localizedDomainInclusion
    (i : S.presentation.atlas.Index) :
    IsAffinoidDomainEmbedding (S.localizedDomainInclusion (S.chartDomain i)) :=
  ⟨i, Iso.refl _, (Category.id_comp _).symm⟩

/-- Affinoid domain embeddings are stable under precomposition with isomorphisms. -/
theorem IsAffinoidDomainEmbedding.iso_comp {U V W : LocalizedCategory.{u, v, w} (K := K)}
    {j : V ⟶ W} (hj : IsAffinoidDomainEmbedding j) (e : U ≅ V) :
    IsAffinoidDomainEmbedding (e.hom ≫ j) := by
  obtain ⟨i, e', rfl⟩ := hj
  exact ⟨i, e ≪≫ e', (Category.assoc _ _ _).symm⟩

end SaturatedAtlasPresentation

end Langlands.Analytic
