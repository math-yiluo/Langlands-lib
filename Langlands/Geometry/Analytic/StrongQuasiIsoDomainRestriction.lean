import Langlands.Geometry.Analytic.StrongNearDomainTransport
import Langlands.Geometry.Analytic.StrongQuasiIsoDomainImage
import Langlands.Geometry.Analytic.SaturatedDomainPreimage

/-! # Restriction of a full quasi-isomorphism to an actual inverse-image domain -/

noncomputable section

universe u v w

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory Set PresentedAffinoidAlgebra IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : SaturatedAtlasPresentation.{u, v, w} K}

set_option maxHeartbeats 400000 in
/-- Domain restriction commutes with the two full analytic inclusions. -/
theorem restrictDomains_comp_domainInclusion (f : A ⟶ B)
    (E : A.AnalyticDomain) (D : B.AnalyticDomain)
    (h : f.MapsOriginalDomainCharts E D) :
    f.restrictDomains E D h ≫ B.domainInclusion D = A.domainInclusion E ≫ f := by
  refine AffinoidAtlasPresentation.StrongHom.ext_of_saturated
    (f := f.restrictDomains E D h ≫ B.domainInclusion D)
    (g := A.domainInclusion E ≫ f) (A.domain E).hasAllLocalDomains rfl ?_
  intro i
  obtain ⟨j, hij⟩ := h i
  have hrestricted := (f.restrictDomainsBaseMap_admissible_iff E D h i j).mpr hij
  have hcomp : (f.restrictDomains E D h ≫ B.domainInclusion D).baseMap ''
      Set.range ((A.domain E).presentation.atlas.chart i) ⊆
        Set.range (B.presentation.atlas.chart j.val) := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact hij ⟨_, ⟨x, rfl⟩, rfl⟩
  refine ⟨j.val, hcomp, ?_⟩
  have hp := originalDomainInclusion_comp_pullback D (f.restrictDomains E D h)
    i j hrestricted hcomp
  have hq := domainInclusion_comp_pullback f E i j.val hij hcomp
  exact hp.trans hq.symm

namespace QuasiIsoDomainRestriction

variable (s : A ⟶ B) (hs : s.IsQuasiIso) (D : B.AnalyticDomain)

/-- The literal inverse-image subset, carrying its proved analytic-domain structure. -/
def preimageDomain : A.AnalyticDomain :=
  ⟨s.baseMap ⁻¹' D.carrier, s.isOriginalChartDomain_preimage A.hasAllLocalDomains D⟩

@[simp]
theorem preimageDomain_carrier :
    (preimageDomain s D).carrier = s.baseMap ⁻¹' D.carrier := rfl

include hs in
/-- Every retained source chart maps onto an entire original target chart
contained in the target domain. -/
theorem mapsOriginalDomainCharts :
    s.MapsOriginalDomainCharts (preimageDomain s D) D := by
  intro i
  let U : LocalDomain A.presentation.atlas :=
    ⟨i.val, Domain.whole K (A.presentation.atlas.algebra i.val)⟩
  have hU : U.locus = Set.range (A.presentation.atlas.chart i.val) := Set.image_univ
  let j := hs.imageOriginalChartIndex B.hasAllLocalDomains U
  have hj : Set.range (B.presentation.atlas.chart j) =
      s.baseMap '' Set.range (A.presentation.atlas.chart i.val) :=
    (hs.range_imageOriginalChartIndex B.hasAllLocalDomains U).trans
      (congrArg (s.baseMap '' ·) hU)
  have hjD : Set.range (B.presentation.atlas.chart j) ⊆ D.carrier := by
    rw [hj]
    rintro _ ⟨x, hx, rfl⟩
    exact i.property hx
  exact ⟨⟨j, hjD⟩, hj.symm.subset⟩

/-- The full strong map between the actual domains, retaining ambient pullbacks. -/
def map : A.domain (preimageDomain s D) ⟶ B.domain D :=
  s.restrictDomains (preimageDomain s D) D (mapsOriginalDomainCharts s hs D)

@[simp]
theorem map_apply_val (x : (preimageDomain s D).carrier) :
    ((map s hs D).baseMap x).val = s.baseMap x.val := rfl

/-- The inverse-image restriction of a full quasi-isomorphism is again one. -/
theorem isQuasiIso : (map s hs D).IsQuasiIso := by
  apply hs.restrictDomains (preimageDomain s D) D (mapsOriginalDomainCharts s hs D)
  exact Set.image_preimage_eq D.carrier hs.1.homeomorph.surjective

/-- The restriction square commutes as complete strong analytic maps. -/
theorem map_comp_domainInclusion :
    map s hs D ≫ B.domainInclusion D = A.domainInclusion (preimageDomain s D) ≫ s :=
  restrictDomains_comp_domainInclusion s (preimageDomain s D) D
    (mapsOriginalDomainCharts s hs D)

end QuasiIsoDomainRestriction

end Langlands.Analytic.SaturatedAtlasPresentation
