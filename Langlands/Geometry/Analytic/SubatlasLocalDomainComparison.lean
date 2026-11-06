import Langlands.Geometry.Analytic.AtlasSubatlas
import Langlands.Geometry.Analytic.AtlasDomainCategory

/-! # Actual bounded local-domain restrictions under subatlas selection -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas

open CategoryTheory Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)
  (P : a.Index → Prop) (hP : a.IsLocallyRefiningSelection P)

/-- Different finite common-chart choices before and after selection yield
the same entire bounded map from every selected containing original chart. -/
theorem subatlas_domainChartRestriction (i j : {i : a.Index // P i})
    (U : Domain K (a.algebra i.val))
    (h : a.chart i.val '' U.locus ⊆ Set.range (a.chart j.val)) :
    (a.subatlas P hP).domainChartRestriction i j U h =
      a.domainChartRestriction i.val j.val U h := by
  let b := a.subatlas P hP
  let c := b.domainImageChartCover i j U h
  apply BoundedAlgHom.ext
  intro x
  apply c.domainCover.algebra_ext_of_restrict_eq
  intro t
  have hs := c.restriction_comp_glueChartRestriction t
  have ho := a.domainChartRestriction_test i.val j.val U h
    (c.domainCover.obj t) (c.domainCover.map t) (c.index t).val
    (c.left_subset t) (c.right_subset t) (c.domainCoverToChart t)
  exact congrArg (fun f : BoundedAlgHom K (a.algebra j.val)
    (c.domainCover.obj t).algebra => f x) (hs.trans ho.symm)

/-- Full-test cancellation upgrades the chart structural comparison to
every actual bounded restriction between selected local full domains. -/
theorem subatlas_domainRestriction (i j : {i : a.Index // P i})
    (U : Domain K (a.algebra i.val)) (V : Domain K (a.algebra j.val))
    (h : a.chart i.val '' U.locus ⊆ a.chart j.val '' V.locus) :
    (a.subatlas P hP).domainRestriction i j U V h =
      a.domainRestriction i.val j.val U V h := by
  apply a.eq_domainRestriction_of_over_base i.val j.val U V h
  exact ((a.subatlas P hP).domainRestriction_comp_baseMap i j U V h).trans
    (a.subatlas_domainChartRestriction P hP i j U _)

/-- Forget only the selection proof; keep the original full-domain algebra,
structural map and literal ambient subset. -/
def subatlasLocalDomain (U : LocalDomain (a.subatlas P hP)) : LocalDomain a :=
  ⟨U.index.val, U.domain⟩

@[simp]
theorem subatlasLocalDomain_algebra (U : LocalDomain (a.subatlas P hP)) :
    (a.subatlasLocalDomain P hP U).algebra = U.algebra := rfl

@[simp]
theorem subatlasLocalDomain_locus (U : LocalDomain (a.subatlas P hP)) :
    (a.subatlasLocalDomain P hP U).locus = U.locus := rfl

@[simp]
theorem subatlasLocalDomain_ambientMap (U : LocalDomain (a.subatlas P hP)) :
    (a.subatlasLocalDomain P hP U).ambientMap = U.ambientMap := rfl

/-- The actual original local-domain inclusion functor. Its arrows use the
constructed original restrictions, which recover every selected restriction. -/
def subatlasLocalDomainFunctor : LocalDomain (a.subatlas P hP) ⥤ LocalDomain a where
  obj := a.subatlasLocalDomain P hP
  map f := LocalDomain.Inclusion.ofSubset _ _ f.subset
  map_id U := @Subsingleton.elim (LocalDomain.Inclusion
    (a.subatlasLocalDomain P hP U) (a.subatlasLocalDomain P hP U)) inferInstance _ _
  map_comp {U _V W} _f _g := @Subsingleton.elim (LocalDomain.Inclusion
    (a.subatlasLocalDomain P hP U) (a.subatlasLocalDomain P hP W)) inferInstance _ _

/-- This equality retains nilpotent and all other algebra information; it is
not inferred from equality of the induced spectrum maps. -/
theorem subatlasLocalDomainFunctor_map_restriction
    {U V : LocalDomain (a.subatlas P hP)} (f : U ⟶ V) :
    ((a.subatlasLocalDomainFunctor P hP).map f).restriction = f.restriction := by
  change a.domainRestriction U.index.val V.index.val U.domain V.domain f.subset = _
  exact (a.subatlas_domainRestriction P hP U.index V.index U.domain V.domain f.subset).symm.trans
    f.restriction_eq.symm

/-- Ambient containment constructs the preimage arrow, and full-test
uniqueness verifies both inverse laws. -/
def fullyFaithfulSubatlasLocalDomainFunctor :
    (a.subatlasLocalDomainFunctor P hP).FullyFaithful where
  preimage f := LocalDomain.Inclusion.ofSubset _ _ f.subset
  map_preimage {U V} _f := @Subsingleton.elim (LocalDomain.Inclusion
    (a.subatlasLocalDomain P hP U) (a.subatlasLocalDomain P hP V)) inferInstance _ _
  preimage_map {U V} _f := @Subsingleton.elim (LocalDomain.Inclusion U V) inferInstance _ _

instance : (a.subatlasLocalDomainFunctor P hP).Full :=
  (a.fullyFaithfulSubatlasLocalDomainFunctor P hP).full

instance : (a.subatlasLocalDomainFunctor P hP).Faithful :=
  (a.fullyFaithfulSubatlasLocalDomainFunctor P hP).faithful

/-- The actual presented-affinoid diagram is preserved on its unchanged
quotient algebras by bounded identity isomorphisms. -/
def subatlasLocalDomainAffinoidNatIso :
    a.subatlasLocalDomainFunctor P hP ⋙ LocalDomain.toAffinoidSpace a ≅
      LocalDomain.toAffinoidSpace (a.subatlas P hP) :=
  NatIso.ofComponents (fun U => Iso.refl (Opposite.op U.algebra)) (by
    intro U V f
    simp only [Iso.refl_hom]
    exact congrArg (fun q : V.algebra ⟶ U.algebra => Quiver.Hom.op q)
      (a.subatlasLocalDomainFunctor_map_restriction P hP f))

end Langlands.Analytic.IndexedAffinoidAtlas
