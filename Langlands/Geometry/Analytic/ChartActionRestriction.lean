import Langlands.Geometry.Analytic.ChartDomainSpectralTests
import Langlands.Geometry.Analytic.DomainSpectralRestriction
import Langlands.Geometry.Analytic.QuasiEtaleDomains
import Langlands.Geometry.Analytic.QuasiEtaleRigidity.StrongNearPostcomposition
import Mathlib.CategoryTheory.Conj

/-! # Analytic action tests on chart subdomains -/

noncomputable section

universe u v z

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory Set Filter Topology BanachSpectrum PresentedAffinoidAlgebra
open AffinoidAtlasPresentation.StrongHom

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X Y : LocalizedCategory.{u, v, v} (K := K)}

private theorem fullChart_contains (S : SaturatedAtlasPresentation.{u, v, v} K)
    (i : S.presentation.atlas.Index) (j : (S.domain (S.chartDomain i)).presentation.atlas.Index) :
    range ((S.domain (S.chartDomain i)).presentation.atlas.chart j) ⊆
      range ((S.domain (S.chartDomain i)).presentation.atlas.chart (chartDomainFullChart S i)) := by
  rw [(chartDomainFullChart_surjective S i).range_eq]
  exact subset_univ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- For a strong map of chart domains, the localized bounded pullback is its
original pullback on the two full charts. -/
theorem chartDomainPullback_localizationFunctor_map
    (i : (presentationOf X).presentation.atlas.Index) (j : (presentationOf Y).presentation.atlas.Index)
    (f : (presentationOf X).domain ((presentationOf X).chartDomain i) ⟶
      (presentationOf Y).domain ((presentationOf Y).chartDomain j)) :
    chartDomainPullback i j (localizationFunctor.map f) =
      f.pullbackAtTop (chartDomainFullChart (presentationOf Y) j) (fullChart_contains _ j)
        (chartDomainFullChart (presentationOf X) i) := by
  unfold chartDomainPullback
  rw [← localizedTopTargetHomEquiv_apply (chartDomainFullChart (presentationOf Y) j)
    (fullChart_contains (presentationOf Y) j) f, Equiv.symm_apply_apply]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- On spectra the bounded chart-domain pullback is the point map of the
localized arrow followed by the target chart inclusion. -/
theorem chartDomainPullback_chart
    (i : (presentationOf X).presentation.atlas.Index) (j : (presentationOf Y).presentation.atlas.Index)
    (f : domainObj X ((presentationOf X).chartDomain i) ⟶
      domainObj Y ((presentationOf Y).chartDomain j))
    (x : BanachSpectrum ((presentationOf X).presentation.atlas.algebra i)) :
    (presentationOf Y).presentation.atlas.chart j
        (comap (chartDomainPullback i j f).toBoundedRingHom x) =
      localizedSpaceFunctor.map (f ≫ domainι Y ((presentationOf Y).chartDomain j))
        (((presentationOf X).domain ((presentationOf X).chartDomain i)).presentation.atlas.chart
          (chartDomainFullChart (presentationOf X) i) x) := by
  let t := chartDomainFullChart (presentationOf Y) j
  let s := chartDomainFullChart (presentationOf X) i
  let A := (presentationOf X).domain ((presentationOf X).chartDomain i)
  let e := localizedTopTargetHomEquiv (A := A) t (fullChart_contains (presentationOf Y) j)
  let a := e.symm f
  have ha : localizationFunctor.map a = f := by
    simpa only [e, localizedTopTargetHomEquiv_apply] using e.apply_symm_apply f
  have hchart := a.chart_comm s t (a.image_chart_top t (fullChart_contains _ j) s) x
  have hpoint := congrArg Subtype.val hchart
  rw [← ha, chartDomainPullback_localizationFunctor_map, CategoryTheory.Functor.map_comp,
    TopCat.comp_app, localizedSpaceFunctor_map, domainι_apply]
  exact hpoint

/-- A nested pair of chart domains carries the actual localized inclusion. -/
def chartDomainInclusion (i j : (presentationOf X).presentation.atlas.Index)
    (h : range ((presentationOf X).presentation.atlas.chart i) ⊆
      range ((presentationOf X).presentation.atlas.chart j)) :
    domainObj X ((presentationOf X).chartDomain i) ⟶
      domainObj X ((presentationOf X).chartDomain j) :=
  localizationFunctor.map ((presentationOf X).domainMap h)

@[reassoc]
theorem chartDomainInclusion_comp (i j : (presentationOf X).presentation.atlas.Index)
    (h : range ((presentationOf X).presentation.atlas.chart i) ⊆
      range ((presentationOf X).presentation.atlas.chart j)) :
    chartDomainInclusion i j h ≫ domainι X ((presentationOf X).chartDomain j) =
      domainι X ((presentationOf X).chartDomain i) := by
  let S := presentationOf X
  let D := S.chartDomain i
  let E := S.chartDomain j
  have hh : D ≤ E := h
  have hcomp : S.domainMap hh ≫ S.domainInclusion E = S.domainInclusion D ≫ 𝟙 S :=
    restrictDomains_comp_domainInclusion (𝟙 S) D E (mapsOriginalDomainCharts_id hh)
  change localizationFunctor.map (S.domainMap hh) ≫
    localizationFunctor.map (S.domainInclusion E) = localizationFunctor.map (S.domainInclusion D)
  rw [← CategoryTheory.Functor.map_comp]
  exact congrArg localizationFunctor.map (hcomp.trans (Category.comp_id _))

theorem chartDomainPullback_inclusion (i j : (presentationOf X).presentation.atlas.Index)
    (h : range ((presentationOf X).presentation.atlas.chart i) ⊆
      range ((presentationOf X).presentation.atlas.chart j)) :
    chartDomainPullback i j (chartDomainInclusion i j h) =
      (presentationOf X).presentation.atlas.restriction i j h := by
  rw [chartDomainInclusion, chartDomainPullback_localizationFunctor_map]
  rfl

private theorem mapsTo_chart_inv (i : (presentationOf X).presentation.atlas.Index) (e : Aut X)
    (h : localizedSpaceFunctor.map e.hom ⁻¹' ((presentationOf X).chartDomain i).carrier =
      ((presentationOf X).chartDomain i).carrier) :
    ∀ x ∈ ((presentationOf X).chartDomain i).carrier,
      localizedSpaceFunctor.map e.inv x ∈ ((presentationOf X).chartDomain i).carrier := by
  intro x hx
  rw [← h]
  let e' := TopCat.homeoOfIso (localizedSpaceFunctor.mapIso e)
  change e' (e'.symm x) ∈ ((presentationOf X).chartDomain i).carrier
  exact (congrArg (fun y : (presentationOf X).presentation.space => y ∈
    ((presentationOf X).chartDomain i).carrier) (e'.apply_symm_apply x)).mpr hx

private def chartPullbackAut (i : (presentationOf X).presentation.atlas.Index)
    (e : Aut (domainObj X ((presentationOf X).chartDomain i))) :
    Aut ((presentationOf X).presentation.atlas.algebra i) where
  hom := chartDomainPullback i i e.hom
  inv := chartDomainPullback i i e.inv
  hom_inv_id := by
    change (chartDomainPullback i i e.inv).comp (chartDomainPullback i i e.hom) = _
    rw [← chartDomainPullback_comp, e.inv_hom_id, chartDomainPullback_id]
    rfl
  inv_hom_id := by
    change (chartDomainPullback i i e.hom).comp (chartDomainPullback i i e.inv) = _
    rw [← chartDomainPullback_comp, e.hom_inv_id, chartDomainPullback_id]
    rfl

/-- Pull back sections by an analytic automorphism on a preserved chart.
Away from chart preservation the family takes the identity automorphism. -/
def preservedChartAut (i : (presentationOf X).presentation.atlas.Index) (e : Aut X) :
    Aut ((presentationOf X).presentation.atlas.algebra i) := by
  classical
  let D := (presentationOf X).chartDomain i
  exact if h : localizedSpaceFunctor.map e.hom ⁻¹' D.carrier = D.carrier then
    chartPullbackAut i (domainRestrictIso e D D (mapsTo_chart_of_preimage_eq i e.hom h)
      (mapsTo_chart_inv i e h))
  else 1

theorem preservedChartAut_hom (i : (presentationOf X).presentation.atlas.Index) (e : Aut X) :
    (preservedChartAut i e).hom = preservedChartPullback i e.hom := by
  classical
  by_cases h : localizedSpaceFunctor.map e.hom ⁻¹' ((presentationOf X).chartDomain i).carrier =
      ((presentationOf X).chartDomain i).carrier
  · rw [preservedChartAut, dite_eq_left h, preservedChartPullback_of_preimage_eq _ _ h]
    rfl
  · simp only [preservedChartAut, preservedChartPullback, dite_eq_right h]
    rfl

private theorem chart_preservedChartAut (i : (presentationOf X).presentation.atlas.Index)
    (e : Aut X) (h : localizedSpaceFunctor.map e.hom ⁻¹' ((presentationOf X).chartDomain i).carrier =
      ((presentationOf X).chartDomain i).carrier)
    (x : BanachSpectrum ((presentationOf X).presentation.atlas.algebra i)) :
    (presentationOf X).presentation.atlas.chart i
        (comap (preservedChartAut i e).hom.toBoundedRingHom x) =
      localizedSpaceFunctor.map e.hom ((presentationOf X).presentation.atlas.chart i x) := by
  rw [preservedChartAut_hom, preservedChartPullback_of_preimage_eq _ _ h,
    chartDomainPullback_chart, domainRestrict_comp, CategoryTheory.Functor.map_comp]
  change localizedSpaceFunctor.map e.hom (localizedSpaceFunctor.map (domainι X _)
    (((presentationOf X).domain ((presentationOf X).chartDomain i)).presentation.atlas.chart
      (chartDomainFullChart (presentationOf X) i) x)) = _
  exact congrArg (fun y : localizedSpaceFunctor.obj X => localizedSpaceFunctor.map e.hom y)
    (domainι_apply ((presentationOf X).chartDomain i) _)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The tests on a fixed parent chart imply every near-identity test on
a smaller chart. The parameter filter need not carry a group structure. -/
theorem eventually_isNear_of_chart_subset {T : Type z} {l : Filter T} (e : T → Aut X)
    (τ : TestTriple (presentationOf X)) (j : (presentationOf X).presentation.atlas.Index)
    (hj : τ.locus ⊆ range ((presentationOf X).presentation.atlas.chart j))
    (hpres : ∀ᶠ t in l, localizedSpaceFunctor.map (e t).hom ⁻¹'
      ((presentationOf X).chartDomain j).carrier = ((presentationOf X).chartDomain j).carrier)
    (hsection : ∀ b, SpectralConvergesOn l (fun t => preservedChartPullback j (e t).hom)
      (BoundedAlgHom.id K _) b) :
    ∀ᶠ t in l, IsNear τ (e t).hom (𝟙 X) := by
  let S := presentationOf X
  let a := S.presentation.atlas
  let i := τ.domain
  let U := a.restrictionDomain i j hj
  have hconv (b : a.algebra j) : SpectralConvergesOn l (fun t => (preservedChartAut j (e t)).hom)
      (BoundedAlgHom.id K _) b := by
    simpa only [preservedChartAut_hom] using hsection b
  have htest := DomainAutomorphism.eventually_spectralBound_sectionMap U hconv
    τ.function τ.bound_pos
  filter_upwards [hpres, htest] with t hpt ht
  obtain ⟨hg, hb⟩ := ht
  let g := preservedChartAut j (e t)
  have hlocus (x : BanachSpectrum (a.algebra j)) :
      localizedSpaceFunctor.map (e t).hom (a.chart j x) ∈ τ.locus ↔ a.chart j x ∈ τ.locus := by
    rw [← chart_preservedChartAut j (e t) hpt]
    change (g⁻¹ • x : BanachSpectrum (a.algebra j)) ∈ U.locus ↔ x ∈ U.locus
    constructor
    · intro hx
      simpa only [smul_inv_smul] using
        DomainAutomorphism.smul_mem_locus U ⟨g, hg⟩ hx
    · exact DomainAutomorphism.smul_mem_locus U
        ⟨g⁻¹, (DomainAutomorphism.locusStabilizer U).inv_mem hg⟩
  have hpi : localizedSpaceFunctor.map (e t).hom ⁻¹' (S.chartDomain i).carrier =
      (S.chartDomain i).carrier := by
    ext x
    change localizedSpaceFunctor.map (e t).hom x ∈ τ.locus ↔ x ∈ τ.locus
    have h (hx : x ∈ range (a.chart j)) :
        localizedSpaceFunctor.map (e t).hom x ∈ τ.locus ↔ x ∈ τ.locus := by
      obtain ⟨y, rfl⟩ := hx
      exact hlocus y
    constructor
    · intro hx
      have hxj : x ∈ localizedSpaceFunctor.map (e t).hom ⁻¹' (S.chartDomain j).carrier :=
        hj hx
      rw [hpt] at hxj
      exact (h hxj).mp hx
    · intro hx
      exact (h (hj hx)).mpr hx
  apply isNear_id_of_spectralBound_preservedChartPullback τ hpi
  let f := domainRestrict (S.chartDomain i) (S.chartDomain i) (e t).hom
    (mapsTo_chart_of_preimage_eq i (e t).hom hpi)
  let k := domainRestrict (S.chartDomain j) (S.chartDomain j) (e t).hom
    (mapsTo_chart_of_preimage_eq j (e t).hom hpt)
  let p := chartDomainInclusion i j hj
  have hcomm : f ≫ p = p ≫ k := by
    let ιi := domainι X (S.chartDomain i)
    let ιj := domainι X (S.chartDomain j)
    have hp : p ≫ ιj = ιi := chartDomainInclusion_comp i j hj
    have hf : f ≫ ιi = ιi ≫ (e t).hom := domainRestrict_comp _ _ _ _
    have hk : k ≫ ιj = ιj ≫ (e t).hom := domainRestrict_comp _ _ _ _
    apply (cancel_mono ιj).1
    calc
      _ = f ≫ ιi := by rw [Category.assoc, hp]
      _ = ιi ≫ (e t).hom := hf
      _ = _ := by rw [Category.assoc, hk, ← Category.assoc, hp]
  have hbounded := congrArg (chartDomainPullback i j) hcomm
  rw [chartDomainPullback_comp, chartDomainPullback_comp, chartDomainPullback_inclusion] at hbounded
  have heq : chartDomainPullback i i f = DomainAutomorphism.stabilizerSectionMap U ⟨g, hg⟩ := by
    apply DomainAutomorphism.boundedHom_ext U
    rw [DomainAutomorphism.stabilizerSectionMap_comp_baseMap]
    change (chartDomainPullback i i f).comp (a.restriction i j hj) =
      (a.restriction i j hj).comp (preservedChartAut j (e t)).hom
    rw [preservedChartAut_hom, preservedChartPullback_of_preimage_eq _ _ hpt]
    exact hbounded
  rw [preservedChartPullback_of_preimage_eq _ _ hpi, heq]
  exact hb

variable {G : Type z} [Group G] [TopologicalSpace G]

/-- It suffices to check charts containing every chart as a subdomain. -/
theorem isContinuousAction_of_chart_subsets (σ : G →* Aut X)
    (h : ∀ i : (presentationOf X).presentation.atlas.Index,
      ∃ j : (presentationOf X).presentation.atlas.Index,
        range ((presentationOf X).presentation.atlas.chart i) ⊆
          range ((presentationOf X).presentation.atlas.chart j) ∧
        (∀ᶠ t in 𝓝 (1 : G), localizedSpaceFunctor.map (σ t).hom ⁻¹'
          ((presentationOf X).chartDomain j).carrier = ((presentationOf X).chartDomain j).carrier) ∧
        (∀ b, SpectralConvergesOn (𝓝 (1 : G)) (fun t => preservedChartPullback j (σ t).hom)
          (BoundedAlgHom.id K _) b)) :
    IsContinuousAction σ := by
  intro τ
  obtain ⟨j, hj, hpres, hs⟩ := h τ.domain
  exact eventually_isNear_of_chart_subset σ τ j hj hpres hs

/-- Continuous analytic actions transport along analytic isomorphisms.
Postcomposition uses the finitely many tests on the compact inverse image
of the target test chart, and precomposition uses the inverse isomorphism. -/
theorem IsContinuousAction.conjAut {σ : G →* Aut X}
    (hσ : IsContinuousAction σ) (e : X ≅ Y) :
    IsContinuousAction (e.conjAut.toMonoidHom.comp σ) := by
  intro τ
  let e' := TopCat.homeoOfIso (localizedSpaceFunctor.mapIso e)
  have hK : IsCompact (e' ⁻¹' τ.locus) :=
    e'.isCompact_preimage.mpr (isCompact_range
      ((presentationOf Y).presentation.atlas.isEmbedding_chart τ.domain).continuous)
  obtain ⟨E, _, hE⟩ := exists_isNear_postcomp e.hom τ hK
  have htests : ∀ᶠ t in 𝓝 (1 : G), ∀ s : E, IsNear s.val (σ t).hom (𝟙 X) :=
    Filter.eventually_all.mpr (fun s => hσ s.val)
  filter_upwards [htests] with t ht
  have hnear := (hE X (σ t).hom (𝟙 X) (fun s hs => ht ⟨s, hs⟩)).precomp e.inv
  change IsNear τ (e.conjAut (σ t)).hom (𝟙 Y)
  rw [Iso.conjAut_apply]
  change IsNear τ (e.inv ≫ (σ t).hom ≫ e.hom) (𝟙 Y)
  simpa only [Category.assoc, Category.id_comp, e.inv_hom_id] using hnear

end Langlands.Analytic.SaturatedAtlasPresentation
