import Langlands.Geometry.Analytic.CoherentStrongSaturationExtension
import Langlands.Geometry.Analytic.CompatibleStrongCategory

/-! # Full pullbacks on local domains and their saturation representatives -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation.StrongHom

open CategoryTheory Set PresentedAffinoidAlgebra IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : AffinoidAtlasPresentation.{u, v, w} K}
  (f : StrongHom A B) (hf : f.HasCoherentPullbacks)

/-- The actual saturation pullback is the original local-domain pullback
through the two complete bounded representative comparisons. -/
theorem saturationExtension_pullback_localDomains
    (U : LocalDomain A.atlas) (V : LocalDomain B.atlas)
    (h : f.baseMap '' U.locus ⊆ V.locus) :
    ((f.saturationExtension hf).pullback
      ⟨U.locus, ⟨U, rfl⟩⟩ ⟨V.locus, ⟨V, rfl⟩⟩
      (by
        change f.baseMap '' range (A.atlas.saturatedChart _) ⊆ range (B.atlas.saturatedChart _)
        rw [A.atlas.range_saturatedChart, B.atlas.range_saturatedChart]
        exact h)).comp (B.atlas.localDomainSaturatedEquiv V).toBoundedAlgHom =
      (A.atlas.localDomainSaturatedEquiv U).toBoundedAlgHom.comp
        (f.localDomainPullback U V h) := by
  let S : A.atlas.localDomainFamily := ⟨U.locus, ⟨U, rfl⟩⟩
  let T : B.atlas.localDomainFamily := ⟨V.locus, ⟨V, rfl⟩⟩
  let e := LocalDomain.isoOfLocusEq U (A.atlas.saturatedRepresentative S)
    (A.atlas.saturatedRepresentative_locus S).symm
  let e' := LocalDomain.isoOfLocusEq V (B.atlas.saturatedRepresentative T)
    (B.atlas.saturatedRepresentative_locus T).symm
  exact (f.localDomainPullback_naturality hf e.inv e'.inv
    (by
      rw [A.atlas.saturatedRepresentative_locus S, B.atlas.saturatedRepresentative_locus T]
      exact h) h).symm

/-- Reexpress the actual saturation pullback on the unchanged original
local-domain algebras through the complete bounded comparisons. -/
def saturationLocalDomainPullback
    (U : LocalDomain A.atlas) (V : LocalDomain B.atlas)
    (h : f.baseMap '' U.locus ⊆ V.locus) :
    BoundedAlgHom K V.algebra U.algebra :=
  (A.atlas.localDomainSaturatedEquiv U).symm.toBoundedAlgHom.comp
    (((f.saturationExtension hf).pullback
      ⟨U.locus, ⟨U, rfl⟩⟩ ⟨V.locus, ⟨V, rfl⟩⟩
      (by
        change f.baseMap '' range (A.atlas.saturatedChart _) ⊆ range (B.atlas.saturatedChart _)
        rw [A.atlas.range_saturatedChart, B.atlas.range_saturatedChart]
        exact h)).comp (B.atlas.localDomainSaturatedEquiv V).toBoundedAlgHom)

theorem saturationLocalDomainPullback_eq
    (U : LocalDomain A.atlas) (V : LocalDomain B.atlas)
    (h : f.baseMap '' U.locus ⊆ V.locus) :
    f.saturationLocalDomainPullback hf U V h = f.localDomainPullback U V h := by
  apply BoundedAlgHom.ext
  intro x
  have he := congrArg (fun z : BoundedAlgHom K V.algebra
    (A.atlas.saturatedRepresentative ⟨U.locus, ⟨U, rfl⟩⟩).algebra =>
      (A.atlas.localDomainSaturatedEquiv U).symm (z x))
        (f.saturationExtension_pullback_localDomains hf U V h)
  exact he.trans ((A.atlas.localDomainSaturatedEquiv U).symm_apply_apply _)

/-- A supplied whole local-domain map satisfying its actual original
structural equation gives the same complete saturation pullback. -/
theorem saturationExtension_pullback_localDomains_of_over_base
    (U : LocalDomain A.atlas) (V : LocalDomain B.atlas)
    (h : f.baseMap '' U.locus ⊆ V.locus)
    (φ : BoundedAlgHom K V.algebra U.algebra)
    (hφ : φ.comp V.domain.baseMap =
      f.localChartPullback U V.index (f.localDomain_parent_admissible U V h)) :
    ((f.saturationExtension hf).pullback
      ⟨U.locus, ⟨U, rfl⟩⟩ ⟨V.locus, ⟨V, rfl⟩⟩
      (by
        change f.baseMap '' range (A.atlas.saturatedChart _) ⊆ range (B.atlas.saturatedChart _)
        rw [A.atlas.range_saturatedChart, B.atlas.range_saturatedChart]
        exact h)).comp (B.atlas.localDomainSaturatedEquiv V).toBoundedAlgHom =
      (A.atlas.localDomainSaturatedEquiv U).toBoundedAlgHom.comp φ := by
  exact (f.saturationExtension_pullback_localDomains hf U V h).trans
    (congrArg (fun z => (A.atlas.localDomainSaturatedEquiv U).toBoundedAlgHom.comp z)
      (f.localDomainPullback_unique U V h φ hφ).symm)

include hf in
/-- Every coefficient chart change from one original parent pullback
identifies the complete constructed map on an arbitrary actual source domain. -/
theorem localChartPullback_eq_of_parent_chart_change
    (U : LocalDomain A.atlas) (j k : B.atlas.Index)
    (hk : f.baseMap '' range (A.atlas.chart U.index) ⊆ range (B.atlas.chart k))
    (h : f.baseMap '' U.locus ⊆ range (B.atlas.chart j))
    (φ : BoundedAlgHom K (B.atlas.algebra j) U.algebra)
    (hφ : B.atlas.IsMapChartChange k j U.algebra
      (U.domain.baseMap.comp (f.pullback U.index k hk)) φ) :
    φ = f.localChartPullback U j h := by
  have hUk : f.baseMap '' U.locus ⊆ range (B.atlas.chart k) :=
    (image_mono (A.atlas.domainSubset_chart U.index U.index U.domain U.domain Subset.rfl)).trans hk
  have he := f.localChartPullback_of_parent_admissible hf U k hk hUk
  have hc : B.atlas.IsMapChartChange k j U.algebra (f.localChartPullback U k hUk) φ := by
    rw [he]
    exact hφ
  have himage (x : BanachSpectrum U.algebra) :
      B.atlas.chart k (BanachSpectrum.comap (f.localChartPullback U k hUk).toBoundedRingHom x) ∈
        range (B.atlas.chart j) := by
    rw [f.localChartPullback_chart]
    exact h ⟨U.ambientMap x, U.range_ambientMap.subset ⟨x, rfl⟩, rfl⟩
  exact (B.atlas.eq_changeMapChart k j U.algebra _ himage φ hc).trans
    (f.localChartPullback_change U k j hUk h himage)

end Langlands.Analytic.AffinoidAtlasPresentation.StrongHom
