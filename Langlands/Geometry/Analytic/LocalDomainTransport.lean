import Langlands.Geometry.Analytic.AtlasHomeomorph
import Langlands.Geometry.Analytic.AtlasReindexing
import Langlands.Geometry.Analytic.AtlasDomainMapChartChange
import Langlands.Geometry.Analytic.AtlasDomainCategory

/-! # Actual local-domain transport between independent ambient universes -/

noncomputable section

universe u v w z t

namespace Langlands.Analytic.IndexedAffinoidAtlas

open CategoryTheory Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)
  {Y : Type z} [TopologicalSpace Y] (e : X ≃ₜ Y)

/-- The coefficient-test chart-change condition is unchanged by an
ambient homeomorphism, including one changing the ambient universe. -/
theorem IsMapChartChange.transport {i j : a.Index} {R : PresentedAffinoidAlgebra K}
    {φ : BoundedAlgHom K (a.algebra i) R} {ψ : BoundedAlgHom K (a.algebra j) R}
    (hψ : a.IsMapChartChange i j R φ ψ) :
    (a.transport e).IsMapChartChange i j R φ ψ := by
  intro T η m hmi hmj α hα
  exact hψ T η m (a.chart_subset_of_transportSubset e m i hmi)
    (a.chart_subset_of_transportSubset e m j hmj) α hα

theorem domain_subset_of_transport (i j : a.Index) (D : Domain K (a.algebra i))
    (h : (a.transport e).chart i '' D.locus ⊆ range ((a.transport e).chart j)) :
    a.chart i '' D.locus ⊆ range (a.chart j) := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨y, hy⟩ := h ⟨x, hx, rfl⟩
  exact ⟨y, e.injective hy⟩

theorem domain_subset_transport (i j : a.Index) (D : Domain K (a.algebra i))
    (h : a.chart i '' D.locus ⊆ range (a.chart j)) :
    (a.transport e).chart i '' D.locus ⊆ range ((a.transport e).chart j) := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨y, hy⟩ := h ⟨x, hx, rfl⟩
  exact ⟨y, congrArg e hy⟩

/-- Canonical reexpression retains the entire original domain map.
The proof transports the coefficient-test law and uses its uniqueness. -/
theorem domainChartRestriction_transport (i j : a.Index) (D : Domain K (a.algebra i))
    (h : a.chart i '' D.locus ⊆ range (a.chart j))
    (h' : (a.transport e).chart i '' D.locus ⊆ range ((a.transport e).chart j)) :
    (a.transport e).domainChartRestriction i j D h' = a.domainChartRestriction i j D h := by
  exact ((a.transport e).domainChartRestriction_eq_changeMapChart i j D h').trans
    ((a.transport e).eq_changeMapChart i j D.algebra D.baseMap
      ((a.transport e).domainBaseMap_image_chart i j D h')
      (a.domainChartRestriction i j D h)
      ((a.domainChartRestriction_isMapChartChange i j D h).transport a e)).symm

namespace LocalDomain

/-- Only the ambient chart is transported. The original domain, algebra
and bounded structural map are unchanged. -/
def transport (U : LocalDomain a) : LocalDomain (a.transport e) :=
  ⟨U.index, U.domain⟩

theorem transport_ambientMap (U : LocalDomain a) (x : BanachSpectrum U.algebra) :
    (transport a e U).ambientMap x = e (U.ambientMap x) := rfl

theorem transport_locus (U : LocalDomain a) :
    (transport a e U).locus = e '' U.locus :=
  (image_image e (a.chart U.index) U.domain.locus).symm

/-- Transport retains every entire actual bounded restriction, not just
its action on the underlying recognized subsets. -/
def transportMap {U V : LocalDomain a} (r : U ⟶ V) :
    transport a e U ⟶ transport a e V where
  subset := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, he⟩ := r.subset ⟨x, hx, rfl⟩
    exact ⟨y, hy, congrArg e he⟩
  restriction := r.restriction
  comp_chart j hU hV :=
    (congrArg (fun φ : BoundedAlgHom K (a.algebra j) V.algebra => r.restriction.comp φ)
      (a.domainChartRestriction_transport e V.index j V.domain
        (a.domain_subset_of_transport e V.index j V.domain hV) hV)).trans
      ((r.comp_chart j (a.domain_subset_of_transport e U.index j U.domain hU)
        (a.domain_subset_of_transport e V.index j V.domain hV)).trans
          (a.domainChartRestriction_transport e U.index j U.domain
            (a.domain_subset_of_transport e U.index j U.domain hU) hU).symm)

@[simp]
theorem transportMap_restriction {U V : LocalDomain a} (r : U ⟶ V) :
    (transportMap a e r).restriction = r.restriction := rfl

def transportFunctor : LocalDomain a ⥤ LocalDomain (a.transport e) where
  obj := transport a e
  map := transportMap a e
  map_id _ := Inclusion.ext rfl
  map_comp _ _ := Inclusion.ext rfl

/-- The reverse uses the same original index and actual domain data;
it is not transport to a separately chosen presentation. -/
def ofTransport (U : LocalDomain (a.transport e)) : LocalDomain a :=
  ⟨U.index, U.domain⟩

theorem ofTransport_ambientMap (U : LocalDomain (a.transport e))
    (x : BanachSpectrum U.algebra) :
    (ofTransport a e U).ambientMap x = e.symm (U.ambientMap x) :=
  (e.symm_apply_apply _).symm

def ofTransportMap {U V : LocalDomain (a.transport e)} (r : U ⟶ V) :
    ofTransport a e U ⟶ ofTransport a e V where
  subset := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, he⟩ := r.subset ⟨x, hx, rfl⟩
    exact ⟨y, hy, e.injective he⟩
  restriction := r.restriction
  comp_chart j hU hV :=
    (congrArg (fun φ : BoundedAlgHom K (a.algebra j) V.algebra => r.restriction.comp φ)
      (a.domainChartRestriction_transport e V.index j V.domain hV
        (a.domain_subset_transport e V.index j V.domain hV)).symm).trans
      ((r.comp_chart j (a.domain_subset_transport e U.index j U.domain hU)
        (a.domain_subset_transport e V.index j V.domain hV)).trans
          (a.domainChartRestriction_transport e U.index j U.domain hU
            (a.domain_subset_transport e U.index j U.domain hU)))

@[simp]
theorem ofTransportMap_restriction {U V : LocalDomain (a.transport e)} (r : U ⟶ V) :
    (ofTransportMap a e r).restriction = r.restriction := rfl

def ofTransportFunctor : LocalDomain (a.transport e) ⥤ LocalDomain a where
  obj := ofTransport a e
  map := ofTransportMap a e
  map_id _ := Inclusion.ext rfl
  map_comp _ _ := Inclusion.ext rfl

/-- The actual full-domain categories are equivalent across arbitrary
ambient universes, retaining all original algebras and bounded arrows. -/
def transportEquivalence : LocalDomain a ≌ LocalDomain (a.transport e) where
  functor := transportFunctor a e
  inverse := ofTransportFunctor a e
  unitIso := NatIso.ofComponents (fun U => Iso.refl U)
    (by intro U V r; exact @Subsingleton.elim (Inclusion U V) inferInstance _ _)
  counitIso := NatIso.ofComponents (fun U => Iso.refl U)
    (by intro U V r; exact @Subsingleton.elim (Inclusion U V) inferInstance _ _)
  functor_unitIso_comp U :=
    @Subsingleton.elim (Inclusion (transport a e U) (transport a e U)) inferInstance _ _

end LocalDomain
end Langlands.Analytic.IndexedAffinoidAtlas
