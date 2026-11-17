import Langlands.Geometry.Analytic.LocalDomainTransport
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Functor.FullyFaithful

/-! # Full local-domain transport between independent atlas-index universes -/

noncomputable section

universe u v w z

namespace Langlands.Analytic.IndexedAffinoidAtlas

open CategoryTheory Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)
  {J : Type z} (e : J ≃ a.Index)

/-- Renaming original chart indices preserves the whole coefficient-test
chart-change condition. -/
theorem IsMapChartChange.reindex {i j : J} {R : PresentedAffinoidAlgebra K}
    {φ : BoundedAlgHom K (a.algebra (e i)) R}
    {ψ : BoundedAlgHom K (a.algebra (e j)) R}
    (hψ : a.IsMapChartChange (e i) (e j) R φ ψ) :
    (a.reindex e).IsMapChartChange i j R φ ψ := by
  intro T η m hmi hmj α hα
  exact hψ T η (e m) hmi hmj α hα

/-- Canonical full-domain reexpression retains the entire original map,
even when reindexing changes the chart-index universe. -/
theorem domainChartRestriction_reindex (i j : J)
    (D : Domain K (a.algebra (e i)))
    (h : a.chart (e i) '' D.locus ⊆ range (a.chart (e j))) :
    (a.reindex e).domainChartRestriction i j D h =
      a.domainChartRestriction (e i) (e j) D h := by
  exact ((a.reindex e).domainChartRestriction_eq_changeMapChart i j D h).trans
    ((a.reindex e).eq_changeMapChart i j D.algebra D.baseMap
      ((a.reindex e).domainBaseMap_image_chart i j D h)
      (a.domainChartRestriction (e i) (e j) D h)
      ((a.domainChartRestriction_isMapChartChange (e i) (e j) D h).reindex a e)).symm

namespace LocalDomain

/-- Read a domain in the reindexed atlas in the old atlas. No algebra or
structural-map cast is needed in this direction. -/
def ofReindex (U : LocalDomain (a.reindex e)) : LocalDomain a :=
  ⟨e U.index, U.domain⟩

@[simp]
theorem ofReindex_locus (U : LocalDomain (a.reindex e)) :
    (ofReindex a e U).locus = U.locus := rfl

theorem ofReindex_ambientMap (U : LocalDomain (a.reindex e))
    (x : BanachSpectrum U.algebra) :
    (ofReindex a e U).ambientMap x = U.ambientMap x := rfl

def ofReindexMap {U V : LocalDomain (a.reindex e)} (r : U ⟶ V) :
    ofReindex a e U ⟶ ofReindex a e V where
  subset := r.subset
  restriction := r.restriction
  comp_chart k hU hV := by
    obtain ⟨j, rfl⟩ := e.surjective k
    exact (congrArg (fun φ : BoundedAlgHom K (a.algebra (e j)) V.algebra =>
      r.restriction.comp φ) (a.domainChartRestriction_reindex e V.index j V.domain hV).symm).trans
        ((r.comp_chart j hU hV).trans (a.domainChartRestriction_reindex e U.index j U.domain hU))

@[simp]
theorem ofReindexMap_restriction {U V : LocalDomain (a.reindex e)} (r : U ⟶ V) :
    (ofReindexMap a e r).restriction = r.restriction := rfl

def ofReindexFunctor : LocalDomain (a.reindex e) ⥤ LocalDomain a where
  obj := ofReindex a e
  map := ofReindexMap a e
  map_id _ := Inclusion.ext rfl
  map_comp _ _ := Inclusion.ext rfl

/-- Every old actual arrow between images returns to the reindexed atlas
with its entire original bounded restriction. -/
def preimageOfReindex {U V : LocalDomain (a.reindex e)}
    (r : ofReindex a e U ⟶ ofReindex a e V) : U ⟶ V where
  subset := r.subset
  restriction := r.restriction
  comp_chart j hU hV :=
    (congrArg (fun φ : BoundedAlgHom K (a.algebra (e j)) V.algebra => r.restriction.comp φ)
      (a.domainChartRestriction_reindex e V.index j V.domain hV)).trans
      ((r.comp_chart (e j) hU hV).trans (a.domainChartRestriction_reindex e U.index j U.domain hU).symm)

def ofReindexFullyFaithful : (ofReindexFunctor a e).FullyFaithful where
  preimage := preimageOfReindex a e
  map_preimage _ := Inclusion.ext rfl
  preimage_map _ := Inclusion.ext rfl

instance : (ofReindexFunctor a e).Full := (ofReindexFullyFaithful a e).full
instance : (ofReindexFunctor a e).Faithful := (ofReindexFullyFaithful a e).faithful

instance : (ofReindexFunctor a e).EssSurj where
  mem_essImage U := by
    obtain ⟨i, D⟩ := U
    obtain ⟨j, rfl⟩ := e.surjective i
    exact ⟨⟨j, D⟩, ⟨Iso.refl _⟩⟩

instance : (ofReindexFunctor a e).IsEquivalence where

/-- The actual full-domain category is independent of the index names
and universe. Fullness retains complete original bounded maps. -/
def reindexEquivalence : LocalDomain (a.reindex e) ≌ LocalDomain a :=
  (ofReindexFunctor a e).asEquivalence

/-- The forward diagram retains actual original algebras and entire
bounded arrows literally. -/
theorem ofReindexFunctor_comp_toAffinoidSpace :
    ofReindexFunctor a e ⋙ toAffinoidSpace a = toAffinoidSpace (a.reindex e) := rfl

/-- The chosen inverse object is compared with the original actual
domain by a constructed entire bounded isomorphism. -/
def reindexCounitEquiv (U : LocalDomain a) :
    BoundedAlgEquiv K ((reindexEquivalence a e).inverse.obj U).algebra U.algebra :=
  boundedEquivOfIso ((reindexEquivalence a e).counitIso.app U)

theorem reindexInverse_locus (U : LocalDomain a) :
    ((reindexEquivalence a e).inverse.obj U).locus = U.locus :=
  locus_eq_of_iso ((reindexEquivalence a e).counitIso.app U)

theorem reindexCounitEquiv_chart (U : LocalDomain a)
    (x : BanachSpectrum ((reindexEquivalence a e).inverse.obj U).algebra) :
    U.ambientMap ((reindexCounitEquiv a e U).symm.spectrumHomeomorph x) =
      ((reindexEquivalence a e).inverse.obj U).ambientMap x :=
  ((reindexEquivalence a e).counitIso.app U).hom.ambientMap_naturality x

/-- Entire inverse-object coefficient comparisons are natural on every
original actual bounded restriction, including nilpotent information. -/
theorem reindexCounitEquiv_naturality {U V : LocalDomain a} (r : U ⟶ V) :
    ((reindexEquivalence a e).inverse.map r).restriction.comp
        (reindexCounitEquiv a e V).symm.toBoundedAlgHom =
      (reindexCounitEquiv a e U).symm.toBoundedAlgHom.comp r.restriction :=
  congrArg Inclusion.restriction ((reindexEquivalence a e).counitIso.hom.naturality r)

end LocalDomain
end Langlands.Analytic.IndexedAffinoidAtlas
