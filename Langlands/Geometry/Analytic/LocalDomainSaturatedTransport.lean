import Langlands.Geometry.Analytic.LocalDomainReindexing
import Langlands.Geometry.Analytic.SaturatedAffinoidAtlas

/-! # Whole local-domain diagrams in a transported saturated atlas -/

noncomputable section

universe u v w z t

namespace Langlands.Analytic.IndexedAffinoidAtlas.LocalDomain

open CategoryTheory Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)
  {Y : Type z} [TopologicalSpace Y] (e : X ≃ₜ Y)
  {J : Type t} (c : J ≃ a.Index)

/-- Actual local full domains are transported first in space and then in
index universe, retaining the full original coefficient diagram. -/
def transportReindexFunctor : LocalDomain a ⥤ LocalDomain ((a.transport e).reindex c) :=
  transportFunctor a e ⋙ (reindexEquivalence (a.transport e) c).inverse

theorem transportReindex_locus (U : LocalDomain a) :
    ((transportReindexFunctor a e c).obj U).locus = e '' U.locus :=
  (reindexInverse_locus (a.transport e) c (transport a e U)).trans
    (transport_locus a e U)

/-- The old algebra maps to the transported actual domain algebra by the
inverse of the full bounded counit comparison. -/
def transportReindexEquiv (U : LocalDomain a) :
    BoundedAlgEquiv K U.algebra ((transportReindexFunctor a e c).obj U).algebra :=
  (reindexCounitEquiv (a.transport e) c (transport a e U)).symm

theorem transportReindexEquiv_chart (U : LocalDomain a)
    (x : BanachSpectrum ((transportReindexFunctor a e c).obj U).algebra) :
    e (U.ambientMap ((transportReindexEquiv a e c U).spectrumHomeomorph x)) =
      ((transportReindexFunctor a e c).obj U).ambientMap x :=
  reindexCounitEquiv_chart (a.transport e) c (transport a e U) x

theorem transportReindexEquiv_naturality {U V : LocalDomain a} (r : U ⟶ V) :
    ((transportReindexFunctor a e c).map r).restriction.comp
        (transportReindexEquiv a e c V).toBoundedAlgHom =
      (transportReindexEquiv a e c U).toBoundedAlgHom.comp r.restriction :=
  reindexCounitEquiv_naturality (a.transport e) c (transportMap a e r)

/-- The literal transported local-domain image is an actual original
index of the target atlas's full-domain saturation. -/
def transportedSaturatedIndex (U : LocalDomain a) :
    ((a.transport e).reindex c).saturatedAtlas.Index :=
  ⟨((transportReindexFunctor a e c).obj U).locus, ⟨_, rfl⟩⟩

theorem range_transportedSaturatedIndex (U : LocalDomain a) :
    range (((a.transport e).reindex c).saturatedAtlas.chart
      (transportedSaturatedIndex a e c U)) = e '' U.locus :=
  (((a.transport e).reindex c).range_saturatedChart _).trans
    (transportReindex_locus a e c U)

/-- The complete original local-domain algebra is compared with the
chosen transported saturated algebra by two constructed bounded
equivalences, retaining all nonreduced coefficients. -/
def transportedSaturatedEquiv (U : LocalDomain a) :
    BoundedAlgEquiv K U.algebra
      (((a.transport e).reindex c).saturatedAtlas.algebra (transportedSaturatedIndex a e c U)) :=
  (transportReindexEquiv a e c U).trans
    (((a.transport e).reindex c).localDomainSaturatedEquiv
      ((transportReindexFunctor a e c).obj U))

theorem transportedSaturatedEquiv_chart (U : LocalDomain a)
    (x : BanachSpectrum (((a.transport e).reindex c).saturatedAtlas.algebra
      (transportedSaturatedIndex a e c U))) :
    e (U.ambientMap ((transportedSaturatedEquiv a e c U).spectrumHomeomorph x)) =
      ((a.transport e).reindex c).saturatedAtlas.chart (transportedSaturatedIndex a e c U) x := by
  let b := (a.transport e).reindex c
  let L := (transportReindexFunctor a e c).obj U
  let S := transportedSaturatedIndex a e c U
  let q := isoOfLocusEq L (b.saturatedRepresentative S) (b.saturatedRepresentative_locus S).symm
  exact (transportReindexEquiv_chart a e c U
    ((b.localDomainSaturatedEquiv L).spectrumHomeomorph x)).trans
      (q.inv.ambientMap_naturality x)

theorem transportedSaturatedIndex_subset {U V : LocalDomain a} (r : U ⟶ V) :
    range (((a.transport e).reindex c).saturatedAtlas.chart
      (transportedSaturatedIndex a e c U)) ⊆
        range (((a.transport e).reindex c).saturatedAtlas.chart
          (transportedSaturatedIndex a e c V)) :=
  (range_transportedSaturatedIndex a e c U).subset.trans
    ((image_mono r.subset).trans (range_transportedSaturatedIndex a e c V).symm.subset)

/-- Every entire original actual restriction commutes with the full
transported saturated coefficient comparisons. -/
theorem transportedSaturatedEquiv_naturality {U V : LocalDomain a} (r : U ⟶ V) :
    (((a.transport e).reindex c).saturatedAtlas.restriction
      (transportedSaturatedIndex a e c U) (transportedSaturatedIndex a e c V)
      (transportedSaturatedIndex_subset a e c r)).comp
        (transportedSaturatedEquiv a e c V).toBoundedAlgHom =
      (transportedSaturatedEquiv a e c U).toBoundedAlgHom.comp r.restriction := by
  let b := (a.transport e).reindex c
  let L := (transportReindexFunctor a e c).obj U
  let M := (transportReindexFunctor a e c).obj V
  let S := transportedSaturatedIndex a e c U
  let T := transportedSaturatedIndex a e c V
  let q := isoOfLocusEq L (b.saturatedRepresentative S) (b.saturatedRepresentative_locus S).symm
  let q' := isoOfLocusEq M (b.saturatedRepresentative T) (b.saturatedRepresentative_locus T).symm
  let p := (transportReindexFunctor a e c).map r
  let s := b.saturatedInclusion S T (transportedSaturatedIndex_subset a e c r)
  have h : s ≫ q'.inv = q.inv ≫ p :=
    @Subsingleton.elim (Inclusion (b.saturatedRepresentative S) M) inferInstance _ _
  have hs :
      (b.saturatedAtlas.restriction S T (transportedSaturatedIndex_subset a e c r)).comp
          (b.localDomainSaturatedEquiv M).toBoundedAlgHom =
        (b.localDomainSaturatedEquiv L).toBoundedAlgHom.comp p.restriction :=
    congrArg Inclusion.restriction h
  apply BoundedAlgHom.ext
  intro x
  exact (congrArg (fun φ : BoundedAlgHom K M.algebra (b.saturatedAtlas.algebra S) =>
    φ ((transportReindexEquiv a e c V) x)) hs).trans
      (congrArg (b.localDomainSaturatedEquiv L)
        (congrArg (fun φ : BoundedAlgHom K V.algebra L.algebra => φ x)
          (transportReindexEquiv_naturality a e c r)))

end Langlands.Analytic.IndexedAffinoidAtlas.LocalDomain
