import Langlands.Geometry.Analytic.RecognizedDomainClosure
import Mathlib.CategoryTheory.Equivalence

/-! # Actual local-domain and recognized-chart category comparison -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas

open CategoryTheory Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

/-- The existing full-domain closure interface is proved for the actual
full recognition atlas; it is not an additional input assumption. -/
theorem fullRecognitionAtlas_hasAllLocalDomains :
    a.fullRecognitionAtlas.HasAllLocalDomains :=
  a.fullRecognitionAtlas_localDomainFamily

/-- Turn each actual local full domain into its constructed recognized
chart, retaining the same literal ambient subset. -/
def fullRecognitionLocalDomainFunctor :
    LocalDomain a.fullRecognitionAtlas ⥤ a.saturatedAtlas.RecognizedSubset where
  obj U := a.fullRecognitionDomainRecognizedSubset U.index U.domain
  map f := ⟨f.subset⟩
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp]
theorem fullRecognitionLocalDomainFunctor_locus (U : LocalDomain a.fullRecognitionAtlas) :
    (a.fullRecognitionLocalDomainFunctor.obj U).locus = U.locus := rfl

/-- An existing recognized chart has its actual whole-domain presentation
inside the same full atlas, with its original algebra unchanged. -/
def fullRecognitionWholeDomain (V : a.saturatedAtlas.RecognizedSubset) :
    LocalDomain a.fullRecognitionAtlas :=
  ⟨V, Domain.whole K V.algebra⟩

@[simp]
theorem fullRecognitionWholeDomain_algebra (V : a.saturatedAtlas.RecognizedSubset) :
    (a.fullRecognitionWholeDomain V).algebra = V.algebra := rfl

@[simp]
theorem fullRecognitionWholeDomain_locus (V : a.saturatedAtlas.RecognizedSubset) :
    (a.fullRecognitionWholeDomain V).locus = V.locus :=
  Set.image_univ.trans V.range_chart

theorem fullRecognitionWholeDomain_ambientMap (V : a.saturatedAtlas.RecognizedSubset)
    (x : BanachSpectrum V.algebra) :
    (a.fullRecognitionWholeDomain V).ambientMap x = V.chart x :=
  congrArg V.chart (BanachSpectrum.ext fun _ => rfl)

/-- Literal recognized inclusions construct actual whole-domain inclusions
and their full bounded restrictions. -/
def fullRecognitionWholeDomainFunctor :
    a.saturatedAtlas.RecognizedSubset ⥤ LocalDomain a.fullRecognitionAtlas where
  obj := a.fullRecognitionWholeDomain
  map {U V} f := LocalDomain.Inclusion.ofSubset _ _ (by
    rw [a.fullRecognitionWholeDomain_locus, a.fullRecognitionWholeDomain_locus]
    exact f.subset)
  map_id V := @Subsingleton.elim
    (LocalDomain.Inclusion (a.fullRecognitionWholeDomain V)
      (a.fullRecognitionWholeDomain V)) inferInstance _ _
  map_comp f g := @Subsingleton.elim
    (LocalDomain.Inclusion _ _) inferInstance _ _

/-- Passing an original recognized inclusion to whole local domains
retains exactly its entire bounded algebra restriction. -/
theorem fullRecognitionWholeDomainFunctor_map_restriction
    {U V : a.saturatedAtlas.RecognizedSubset} (f : U ⟶ V) :
    (a.fullRecognitionWholeDomainFunctor.map f).restriction = f.restriction := by
  let q := a.fullRecognitionWholeDomainFunctor.map f
  have h := a.fullRecognitionAtlas.domainRestriction_comp_baseMap U V
    (Domain.whole K U.algebra) (Domain.whole K V.algebra) q.subset
  have hc := a.fullRecognitionAtlas.domainChartRestriction_of_chartSubset U V
    (Domain.whole K U.algebra)
    (a.fullRecognitionAtlas.domainSubset_chart U V _ _ q.subset)
    (U.range_chart.subset.trans (f.subset.trans V.range_chart.symm.subset))
  exact (q.restriction_eq.trans h).trans hc

/-- The round trip to a recognized chart and its actual whole presentation
is the canonical full local-domain isomorphism on the same ambient locus. -/
def fullRecognitionLocalDomainUnitIso :
    𝟭 (LocalDomain a.fullRecognitionAtlas) ≅
      a.fullRecognitionLocalDomainFunctor ⋙ a.fullRecognitionWholeDomainFunctor :=
  NatIso.ofComponents
    (fun U => LocalDomain.isoOfLocusEq U
      (a.fullRecognitionWholeDomain (a.fullRecognitionLocalDomainFunctor.obj U))
      (a.fullRecognitionWholeDomain_locus
        (a.fullRecognitionLocalDomainFunctor.obj U)).symm)
    (by
      intro U V f
      exact @Subsingleton.elim (LocalDomain.Inclusion U
        (a.fullRecognitionWholeDomain (a.fullRecognitionLocalDomainFunctor.obj V)))
        inferInstance _ _)

/-- The other round trip gives literal recognized inclusions in both
directions, with all inverse identities proved by inclusion uniqueness. -/
def fullRecognitionLocalDomainCounitComponent (V : a.saturatedAtlas.RecognizedSubset) :
    a.fullRecognitionLocalDomainFunctor.obj (a.fullRecognitionWholeDomain V) ≅ V where
  hom := ⟨(a.fullRecognitionWholeDomain_locus V).subset⟩
  inv := ⟨(a.fullRecognitionWholeDomain_locus V).symm.subset⟩
  hom_inv_id := @Subsingleton.elim (RecognizedSubset.Inclusion _ _) inferInstance _ _
  inv_hom_id := @Subsingleton.elim (RecognizedSubset.Inclusion _ _) inferInstance _ _

def fullRecognitionLocalDomainCounitIso :
    a.fullRecognitionWholeDomainFunctor ⋙ a.fullRecognitionLocalDomainFunctor ≅
      𝟭 a.saturatedAtlas.RecognizedSubset :=
  NatIso.ofComponents (a.fullRecognitionLocalDomainCounitComponent) (by
    intro U V f
    exact @Subsingleton.elim (RecognizedSubset.Inclusion _ _) inferInstance _ _)

/-- Actual local-domain presentations and recognized charts give equivalent
inclusion categories, using the constructed domain recognition functor. -/
def fullRecognitionLocalDomainEquivalence :
    LocalDomain a.fullRecognitionAtlas ≌ a.saturatedAtlas.RecognizedSubset where
  functor := a.fullRecognitionLocalDomainFunctor
  inverse := a.fullRecognitionWholeDomainFunctor
  unitIso := a.fullRecognitionLocalDomainUnitIso
  counitIso := a.fullRecognitionLocalDomainCounitIso
  functor_unitIso_comp U := @Subsingleton.elim
    (RecognizedSubset.Inclusion (a.fullRecognitionLocalDomainFunctor.obj U)
      (a.fullRecognitionLocalDomainFunctor.obj U)) inferInstance _ _

theorem fullRecognitionWholeDomainFunctor_toAffinoidSpace :
    a.fullRecognitionWholeDomainFunctor ⋙ LocalDomain.toAffinoidSpace a.fullRecognitionAtlas =
      RecognizedSubset.toAffinoidSpace a.saturatedAtlas := by
  refine Functor.hext (fun _ => rfl) ?_
  intro U V f
  exact heq_of_eq (congrArg (fun q : V.algebra ⟶ U.algebra => Quiver.Hom.op q)
    (a.fullRecognitionWholeDomainFunctor_map_restriction f))

/-- The category comparison identifies the whole original diagram of
actual affine algebras, with its bounded arrows, by a natural isomorphism. -/
def fullRecognitionLocalDomainAffinoidNatIso :
    LocalDomain.toAffinoidSpace a.fullRecognitionAtlas ≅
      a.fullRecognitionLocalDomainFunctor ⋙
        RecognizedSubset.toAffinoidSpace a.saturatedAtlas :=
  (LocalDomain.toAffinoidSpace a.fullRecognitionAtlas).leftUnitor.symm ≪≫
    Functor.isoWhiskerRight (a.fullRecognitionLocalDomainUnitIso)
      (LocalDomain.toAffinoidSpace a.fullRecognitionAtlas) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (a.fullRecognitionLocalDomainFunctor)
      (eqToIso (a.fullRecognitionWholeDomainFunctor_toAffinoidSpace))

/-- The equivalence's unit gives actual bounded inverse maps between every
original local-domain algebra and its constructed recognized algebra. -/
def fullRecognitionLocalDomainAlgebraEquiv (U : LocalDomain a.fullRecognitionAtlas) :
    BoundedAlgEquiv K U.algebra (a.fullRecognitionLocalDomainFunctor.obj U).algebra :=
  LocalDomain.boundedEquivOfIso (a.fullRecognitionLocalDomainUnitIso.app U)

/-- The comparison is natural for the complete bounded algebra maps of
every actual local-domain inclusion, including all nonreduced information. -/
theorem fullRecognitionLocalDomainAlgebraEquiv_naturality
    {U V : LocalDomain a.fullRecognitionAtlas} (f : U ⟶ V) :
    (a.fullRecognitionLocalDomainAlgebraEquiv U).toBoundedAlgHom.comp f.restriction =
      (a.fullRecognitionLocalDomainFunctor.map f).restriction.comp
        (a.fullRecognitionLocalDomainAlgebraEquiv V).toBoundedAlgHom := by
  have h := congrArg LocalDomain.Inclusion.restriction
    ((a.fullRecognitionLocalDomainUnitIso).inv.naturality f)
  exact h.symm.trans (congrArg
    (fun q : BoundedAlgHom K (a.fullRecognitionLocalDomainFunctor.obj V).algebra
      (a.fullRecognitionLocalDomainFunctor.obj U).algebra =>
        q.comp (a.fullRecognitionLocalDomainAlgebraEquiv V).toBoundedAlgHom)
    (a.fullRecognitionWholeDomainFunctor_map_restriction
      (a.fullRecognitionLocalDomainFunctor.map f)))

/-- The actual comparison of algebras identifies the two ambient charts
on every spectrum point, over the unchanged literal local-domain locus. -/
theorem fullRecognitionLocalDomainAlgebraEquiv_chart
    (U : LocalDomain a.fullRecognitionAtlas)
    (x : BanachSpectrum (a.fullRecognitionLocalDomainFunctor.obj U).algebra) :
    (a.fullRecognitionLocalDomainFunctor.obj U).chart x =
      U.ambientMap ((a.fullRecognitionLocalDomainAlgebraEquiv U).spectrumHomeomorph x) :=
  (((a.fullRecognitionLocalDomainUnitIso.app U).inv.ambientMap_naturality x).trans
    (a.fullRecognitionWholeDomain_ambientMap
      (a.fullRecognitionLocalDomainFunctor.obj U) x)).symm

end Langlands.Analytic.IndexedAffinoidAtlas
