import Langlands.Geometry.Analytic.AffinoidPushoutSpectralTests
import Langlands.Geometry.Analytic.NearIdentityDomainRestriction
import Langlands.Geometry.Analytic.QuasiEtaleFiniteChartCover
import Langlands.Geometry.Analytic.TopChartSpectralTests

/-! # Spectral tests on literal chart domains -/

noncomputable section

universe u v z

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory Set Filter Topology BanachSpectrum PresentedAffinoidAlgebra
open AffinoidAtlasPresentation.StrongHom

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X Y Z : LocalizedCategory.{u, v, v} (K := K)}

private theorem chartDomainFullChart_contains (A : SaturatedAtlasPresentation.{u, v, v} K)
    (i : A.presentation.atlas.Index) (j : (A.domain (A.chartDomain i)).presentation.atlas.Index) :
    range ((A.domain (A.chartDomain i)).presentation.atlas.chart j) ⊆
      range ((A.domain (A.chartDomain i)).presentation.atlas.chart (chartDomainFullChart A i)) := by
  rw [(chartDomainFullChart_surjective A i).range_eq]
  exact subset_univ _

/-- The bounded pullback of a localized arrow between two actual chart domains,
computed on their retained whole charts. -/
def chartDomainPullback (i : (presentationOf X).presentation.atlas.Index)
    (j : (presentationOf Y).presentation.atlas.Index)
    (φ : domainObj X ((presentationOf X).chartDomain i) ⟶
      domainObj Y ((presentationOf Y).chartDomain j)) :
    BoundedAlgHom K ((presentationOf Y).presentation.atlas.algebra j)
      ((presentationOf X).presentation.atlas.algebra i) :=
  ((localizedTopTargetHomEquiv (chartDomainFullChart (presentationOf Y) j)
    (chartDomainFullChart_contains (presentationOf Y) j)).symm φ).pullbackAtTop
      (chartDomainFullChart (presentationOf Y) j) (chartDomainFullChart_contains (presentationOf Y) j)
      (chartDomainFullChart (presentationOf X) i)

@[simp]
theorem chartDomainPullback_id (i : (presentationOf X).presentation.atlas.Index) :
    chartDomainPullback i i (𝟙 (domainObj X ((presentationOf X).chartDomain i))) =
      BoundedAlgHom.id K ((presentationOf X).presentation.atlas.algebra i) := by
  let D := (presentationOf X).domain ((presentationOf X).chartDomain i)
  let j := chartDomainFullChart (presentationOf X) i
  let e := localizedTopTargetHomEquiv (A := D) j (chartDomainFullChart_contains (presentationOf X) i)
  have h : e.symm (𝟙 (localizationFunctor.obj D)) = 𝟙 D := by
    apply e.injective
    rw [Equiv.apply_symm_apply]
    change 𝟙 _ = localizedTopTargetHomEquiv j _ (𝟙 D)
    rw [localizedTopTargetHomEquiv_apply, CategoryTheory.Functor.map_id]
  change (e.symm (𝟙 _)).pullbackAtTop j _ j = _
  rw [h]
  exact D.presentation.atlas.restriction_id j (subset_rfl)

/-- On the full charts the pullback of a composite is the composite
of the two bounded pullbacks in the opposite order. -/
theorem chartDomainPullback_comp (i : (presentationOf X).presentation.atlas.Index)
    (j : (presentationOf Y).presentation.atlas.Index)
    (k : (presentationOf Z).presentation.atlas.Index)
    (φ : domainObj X ((presentationOf X).chartDomain i) ⟶
      domainObj Y ((presentationOf Y).chartDomain j))
    (ψ : domainObj Y ((presentationOf Y).chartDomain j) ⟶
      domainObj Z ((presentationOf Z).chartDomain k)) :
    chartDomainPullback i k (φ ≫ ψ) = (chartDomainPullback i j φ).comp (chartDomainPullback j k ψ) := by
  let i' := chartDomainFullChart (presentationOf X) i
  let j' := chartDomainFullChart (presentationOf Y) j
  let k' := chartDomainFullChart (presentationOf Z) k
  let hj := chartDomainFullChart_contains (presentationOf Y) j
  let hk := chartDomainFullChart_contains (presentationOf Z) k
  let a := (localizedTopTargetHomEquiv j' hj).symm φ
  let b := (localizedTopTargetHomEquiv k' hk).symm ψ
  have h : (localizedTopTargetHomEquiv k' hk).symm (φ ≫ ψ) = a ≫ b := by
    apply (localizedTopTargetHomEquiv k' hk).injective
    rw [Equiv.apply_symm_apply, localizedTopTargetHomEquiv_apply, CategoryTheory.Functor.map_comp]
    have ha : localizationFunctor.map a = φ := by
      simpa only [localizedTopTargetHomEquiv_apply] using
        (localizedTopTargetHomEquiv j' hj).apply_symm_apply φ
    have hb : localizationFunctor.map b = ψ := by
      simpa only [localizedTopTargetHomEquiv_apply] using
        (localizedTopTargetHomEquiv k' hk).apply_symm_apply ψ
    rw [ha, hb]
  change ((localizedTopTargetHomEquiv k' hk).symm (φ ≫ ψ)).pullbackAtTop k' hk i' = _
  rw [h]
  exact pullbackAtTop_comp a b j' k' hj hk i'

/-- Preimage equality for a chart yields an actual restriction to that chart. -/
theorem mapsTo_chart_of_preimage_eq (i : (presentationOf X).presentation.atlas.Index)
    (φ : X ⟶ X) (h : localizedSpaceFunctor.map φ ⁻¹' ((presentationOf X).chartDomain i).carrier =
      ((presentationOf X).chartDomain i).carrier) :
    ∀ x ∈ ((presentationOf X).chartDomain i).carrier,
      localizedSpaceFunctor.map φ x ∈ ((presentationOf X).chartDomain i).carrier := by
  intro x hx
  change x ∈ localizedSpaceFunctor.map φ ⁻¹' ((presentationOf X).chartDomain i).carrier
  rw [h]
  exact hx

/-- The bounded pullback on a preserved chart, extended by the identity away
from the event of preservation for use in filter convergence. -/
def preservedChartPullback (i : (presentationOf X).presentation.atlas.Index) (φ : X ⟶ X) :
    BoundedAlgHom K ((presentationOf X).presentation.atlas.algebra i)
      ((presentationOf X).presentation.atlas.algebra i) := by
  classical
  let D := (presentationOf X).chartDomain i
  exact if h : localizedSpaceFunctor.map φ ⁻¹' D.carrier = D.carrier then
    chartDomainPullback i i (domainRestrict D D φ (mapsTo_chart_of_preimage_eq i φ h))
  else BoundedAlgHom.id K _

theorem preservedChartPullback_of_preimage_eq (i : (presentationOf X).presentation.atlas.Index)
    (φ : X ⟶ X) (h : localizedSpaceFunctor.map φ ⁻¹' ((presentationOf X).chartDomain i).carrier =
      ((presentationOf X).chartDomain i).carrier) :
    preservedChartPullback i φ = chartDomainPullback i i
      (domainRestrict _ _ φ (mapsTo_chart_of_preimage_eq i φ h)) := by
  classical
  exact dite_eq_left h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Ambient nearness implies a spectral bound for the full chart restriction. -/
theorem IsNear.spectralBound_preservedChartPullback (τ : TestTriple (presentationOf X))
    {φ : X ⟶ X} (h : IsNear τ φ (𝟙 X)) :
    SpectralBound (preservedChartPullback τ.domain φ τ.function - τ.function) τ.bound := by
  let D := (presentationOf X).chartDomain τ.domain
  let A := (presentationOf X).domain D
  let i := chartDomainFullChart (presentationOf X) τ.domain
  let hi := chartDomainFullChart_contains (presentationOf X) τ.domain
  let τ' : TestTriple A := ⟨i, τ.function, τ.bound, τ.bound_pos⟩
  have he : τ'.ambient = τ := rfl
  have hpre := h.preimage_eq
  rw [CategoryTheory.Functor.map_id, TopCat.coe_id, Set.preimage_id] at hpre
  change localizedSpaceFunctor.map φ ⁻¹' D.carrier = D.carrier at hpre
  let ψ := domainRestrict D D φ (mapsTo_chart_of_preimage_eq τ.domain φ hpre)
  have hψ : IsNear τ' ψ (𝟙 (domainObj X D)) :=
    IsNear.domainRestrict_id D τ' φ _ (he.symm ▸ h)
  let e := localizedTopTargetHomEquiv (A := A) i hi
  have ha : localizationFunctor.map (e.symm ψ) = ψ := by
    simpa only [e, localizedTopTargetHomEquiv_apply] using e.apply_symm_apply ψ
  have hb : localizationFunctor.map (𝟙 A) = 𝟙 (domainObj X D) :=
    CategoryTheory.Functor.map_id _ _
  have hψ' : IsNear τ' (localizationFunctor.map (e.symm ψ)) (localizationFunctor.map (𝟙 A)) := by
    rw [ha, hb]
    exact hψ
  let f : A.presentation.atlas.algebra i := τ.function
  have hs := (isNear_greatestChart_iff i i hi hi (e.symm ψ) (𝟙 A) f τ.bound_pos).mp hψ'
  rw [preservedChartPullback_of_preimage_eq _ _ hpre]
  change SpectralBound ((e.symm ψ).pullbackAtTop i hi i f - f) τ.bound
  have hid : (𝟙 A : A ⟶ A).pullbackAtTop i hi i = BoundedAlgHom.id K _ :=
    A.presentation.atlas.restriction_id i (subset_rfl)
  rw [hid, BoundedAlgHom.id_apply] at hs
  exact hs

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Preservation of a chart and the spectral estimate on its actual
restriction imply the ambient near-identity test. -/
theorem isNear_id_of_spectralBound_preservedChartPullback (τ : TestTriple (presentationOf X))
    {φ : X ⟶ X} (hpre : localizedSpaceFunctor.map φ ⁻¹'
      ((presentationOf X).chartDomain τ.domain).carrier =
        ((presentationOf X).chartDomain τ.domain).carrier)
    (hbound : SpectralBound (preservedChartPullback τ.domain φ τ.function - τ.function) τ.bound) :
    IsNear τ φ (𝟙 X) := by
  let B := presentationOf X
  let D := B.chartDomain τ.domain
  let A := B.domain D
  let i := chartDomainFullChart B τ.domain
  let hi := chartDomainFullChart_contains B τ.domain
  let τ' : TestTriple A := ⟨i, τ.function, τ.bound, τ.bound_pos⟩
  let ψ := domainRestrict D D φ (mapsTo_chart_of_preimage_eq τ.domain φ hpre)
  let e := localizedTopTargetHomEquiv (A := A) i hi
  let b : A ⟶ A := e.symm ψ
  have hb : localizationFunctor.map b = ψ := by
    simpa only [b, e, localizedTopTargetHomEquiv_apply] using e.apply_symm_apply ψ
  let f : A.presentation.atlas.algebra i := τ.function
  rw [preservedChartPullback_of_preimage_eq _ _ hpre] at hbound
  change SpectralBound (b.pullbackAtTop i hi i f - f) τ.bound at hbound
  obtain ⟨r, hr⟩ := exists_localizedRightFraction (A := B) (B := B) φ
  let T := r.X'
  let s := r.s
  let a := r.f
  let E := QuasiIsoDomainRestriction.preimageDomain s D
  let q : T.domain E ⟶ A := QuasiIsoDomainRestriction.map s r.hs D
  have hsa : localizationFunctor.map s ≫ φ = localizationFunctor.map a := by
    rw [hr]
    exact localizationFunctor_map_s_comp_localizedRightFraction r
  have hpa := numerator_point_eq_of_fraction_equation s a φ hsa
  have hpre' : a.baseMap ⁻¹' τ.locus = s.baseMap ⁻¹' τ.locus := by
    ext x
    change a.baseMap x ∈ D.carrier ↔ s.baseMap x ∈ D.carrier
    rw [← hpa]
    change s.baseMap x ∈ localizedSpaceFunctor.map φ ⁻¹' D.carrier ↔ _
    rw [hpre]
  have hm : a.MapsOriginalDomainCharts E D := by
    intro k
    refine ⟨i, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    have hx' : x ∈ s.baseMap ⁻¹' τ.locus := k.property hx
    rw [← hpre'] at hx'
    exact hx'
  let a' : T.domain E ⟶ A := a.restrictDomains E D hm
  have ha'sq : a' ≫ B.domainInclusion D = T.domainInclusion E ≫ a :=
    restrictDomains_comp_domainInclusion a E D hm
  have hq := QuasiIsoDomainRestriction.isQuasiIso s r.hs D
  have hqsq : q ≫ B.domainInclusion D = T.domainInclusion E ≫ s :=
    QuasiIsoDomainRestriction.map_comp_domainInclusion s r.hs D
  have hψ := eq_domainFraction_of_squares D D s a φ hsa (T.domainInclusion E) q hq a'
    hqsq ha'sq ψ (domainRestrict_comp D D φ _)
  have ha' : a' = q ≫ b := by
    apply (localizedTopTargetHomEquiv (A := T.domain E) (B := A) i hi).injective
    simp only [localizedTopTargetHomEquiv_apply, CategoryTheory.Functor.map_comp, hb]
    rw [hψ]
    exact (localizationFunctor_map_s_comp_localizedRightFraction
      (MorphismProperty.RightFraction.mk q hq a')).symm
  have hstrong : StrongNear τ a s := by
    refine ⟨hpre', ?_, ?_⟩
    · intro x hx
      have hxE : x ∈ E.carrier := by
        change x ∈ s.baseMap ⁻¹' τ.locus
        rw [← hpre']
        exact hx
      obtain ⟨k, y, hy⟩ := (T.domain E).presentation.atlas.exists_mem_range_chart
        (⟨x, hxE⟩ : E.carrier)
      have hks : s.baseMap '' range (T.presentation.atlas.chart k.val) ⊆ τ.locus := by
        rintro _ ⟨z, hz, rfl⟩
        exact k.property hz
      have hka : a.baseMap '' range (T.presentation.atlas.chart k.val) ⊆ τ.locus := by
        rintro _ ⟨z, hz, rfl⟩
        change z ∈ a.baseMap ⁻¹' τ.locus
        rw [hpre']
        exact k.property hz
      exact ⟨k.val, ⟨hka, hks⟩, y, congrArg Subtype.val hy⟩
    · intro k hk p
      let k' : (T.domain E).presentation.atlas.Index :=
        ⟨k, fun x hx => hk.2 ⟨x, hx, rfl⟩⟩
      have ha := domainInclusion_comp_pullback a E k' τ.domain hk.1
        ((isTestPiece_precomp_domainInclusion_iff τ a s E k').mpr hk).1
      have hs := domainInclusion_comp_pullback s E k' τ.domain hk.2
        ((isTestPiece_precomp_domainInclusion_iff τ a s E k').mpr hk).2
      have hpa' := comp_domainInclusion_pullback τ' a' k'
        (a'.image_chart_top i hi k') (by
          rw [ha'sq]
          exact ((isTestPiece_precomp_domainInclusion_iff τ a s E k').mpr hk).1)
      have hpq := comp_domainInclusion_pullback τ' q k'
        (q.image_chart_top i hi k') (by
          rw [hqsq]
          exact ((isTestPiece_precomp_domainInclusion_iff τ a s E k').mpr hk).2)
      have pullback_eq {F F' : T.domain E ⟶ B} (heq : F = F')
          (hF : F.baseMap '' range ((T.domain E).presentation.atlas.chart k') ⊆ τ.locus)
          (hF' : F'.baseMap '' range ((T.domain E).presentation.atlas.chart k') ⊆ τ.locus) :
          F.pullback k' τ.domain hF = F'.pullback k' τ.domain hF' := by
        subst F'
        rfl
      rw [← ha, ← hs, (pullback_eq ha'sq.symm _ _).trans hpa',
        (pullback_eq hqsq.symm _ _).trans hpq]
      change p (a'.pullbackAtTop i hi k' f - q.pullbackAtTop i hi k' f) ≤ τ.bound
      rw [ha', pullbackAtTop_comp q b i i hi hi]
      let m := q.pullbackAtTop i hi k'
      change p (m (b.pullbackAtTop i hi i f) - m f) ≤ τ.bound
      rw [← map_sub]
      exact hbound (comap m.toBoundedRingHom p)
  exact ⟨T, s, r.hs, a, s, hr, (localizedQuasiIso_inv_hom_id s r.hs).symm, hstrong⟩

/-- A continuous analytic action has uniformly small displacement on each
section of each actual chart, on its eventual preservation event. -/
theorem IsContinuousAction.spectralConvergesOn_preservedChartPullback
    {G : Type z} [Group G] [TopologicalSpace G] {σ : G →* Aut X}
    (hσ : IsContinuousAction σ) (i : (presentationOf X).presentation.atlas.Index)
    (f : (presentationOf X).presentation.atlas.algebra i) :
    SpectralConvergesOn (𝓝 (1 : G)) (fun a => preservedChartPullback i (σ a).hom)
      (BoundedAlgHom.id K _) f := by
  intro ε hε
  let τ : TestTriple (presentationOf X) := ⟨i, f, ε, hε⟩
  filter_upwards [hσ τ] with a ha
  change IsNear τ (σ a).hom (𝟙 X) at ha
  exact ha.spectralBound_preservedChartPullback

end Langlands.Analytic.SaturatedAtlasPresentation
