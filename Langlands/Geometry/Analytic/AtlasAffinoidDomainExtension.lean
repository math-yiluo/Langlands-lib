import Langlands.Geometry.Analytic.StrongQuasiIsoComposition
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartDomainComposition
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainComparison
import Mathlib.CategoryTheory.Equivalence

/-! # Full affinoid domains along original atlas chart containments -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas

open CategoryTheory PresentedAffinoidAlgebra Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

/-- The relative chart domain carries its actual subspace topology. -/
def restrictionSpectrumHomeomorph (i j : a.Index)
    (h : Set.range (a.chart i) ⊆ Set.range (a.chart j)) :
    BanachSpectrum (a.algebra i) ≃ₜ (a.restrictionDomain i j h).locus :=
  (a.isEmbedding_restriction i j h).toHomeomorph.trans
    (Homeomorph.setCongr (a.range_restriction i j h))

@[simp]
theorem restrictionSpectrumHomeomorph_apply_coe (i j : a.Index)
    (h : Set.range (a.chart i) ⊆ Set.range (a.chart j))
    (x : BanachSpectrum (a.algebra i)) :
    (a.restrictionSpectrumHomeomorph i j h x : BanachSpectrum (a.algebra j)) =
      BanachSpectrum.comap (a.restriction i j h).toBoundedRingHom x := rfl

/-- Extend a full domain along an original containing chart. The algebra is
unchanged and the structural bounded map is composed with the original restriction. -/
def extendDomain (i j : a.Index)
    (h : Set.range (a.chart i) ⊆ Set.range (a.chart j))
    (U : Domain K (a.algebra i)) : Domain K (a.algebra j) where
  algebra := U.algebra
  baseMap := U.baseMap.comp (a.restriction i j h)
  locus := BanachSpectrum.comap (a.restriction i j h).toBoundedRingHom '' U.locus
  represents := (a.restriction_represents i j h).comp_of_injective U.represents
    (a.isEmbedding_restriction i j h).injective

@[simp]
theorem extendDomain_algebra (i j : a.Index)
    (h : Set.range (a.chart i) ⊆ Set.range (a.chart j))
    (U : Domain K (a.algebra i)) : (a.extendDomain i j h U).algebra = U.algebra := rfl

@[simp]
theorem extendDomain_baseMap (i j : a.Index)
    (h : Set.range (a.chart i) ⊆ Set.range (a.chart j))
    (U : Domain K (a.algebra i)) :
    (a.extendDomain i j h U).baseMap = U.baseMap.comp (a.restriction i j h) := rfl

@[simp]
theorem extendDomain_locus (i j : a.Index)
    (h : Set.range (a.chart i) ⊆ Set.range (a.chart j))
    (U : Domain K (a.algebra i)) :
    (a.extendDomain i j h U).locus =
      BanachSpectrum.comap (a.restriction i j h).toBoundedRingHom '' U.locus := rfl

theorem extendDomain_locus_subset (i j : a.Index)
    (h : Set.range (a.chart i) ⊆ Set.range (a.chart j))
    (U : Domain K (a.algebra i)) :
    (a.extendDomain i j h U).locus ⊆ (a.restrictionDomain i j h).locus := by
  rintro _ ⟨x, _, rfl⟩
  exact (a.restriction_represents i j h).hasImageIn x

/-- Extension describes exactly the same subset of the ambient atlas space. -/
theorem chart_image_extendDomain_locus (i j : a.Index)
    (h : Set.range (a.chart i) ⊆ Set.range (a.chart j))
    (U : Domain K (a.algebra i)) :
    a.chart j '' (a.extendDomain i j h U).locus = a.chart i '' U.locus := by
  ext x
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, (a.restriction_chart i j h y).symm⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨_, ⟨y, hy, rfl⟩, a.restriction_chart i j h y⟩

/-- The inclusion into the original relative chart domain uses the inner
domain's actual structural bounded map. -/
def extendDomainInclusion (i j : a.Index)
    (h : Set.range (a.chart i) ⊆ Set.range (a.chart j))
    (U : Domain K (a.algebra i)) :
    a.extendDomain i j h U ⟶ a.restrictionDomain i j h where
  restriction := U.baseMap
  comp_baseMap := rfl

@[simp]
theorem extendDomainInclusion_restriction (i j : a.Index)
    (h : Set.range (a.chart i) ⊆ Set.range (a.chart j))
    (U : Domain K (a.algebra i)) :
    (a.extendDomainInclusion i j h U).restriction = U.baseMap := rfl

/-- Extension preserves actual represented algebras and bounded restrictions. -/
def extendDomainFunctor (i j : a.Index)
    (h : Set.range (a.chart i) ⊆ Set.range (a.chart j)) :
    Domain K (a.algebra i) ⥤ Domain K (a.algebra j) where
  obj := a.extendDomain i j h
  map {U V} f := ⟨f.restriction, by
    change f.restriction.comp (V.baseMap.comp (a.restriction i j h)) =
      U.baseMap.comp (a.restriction i j h)
    rw [← BoundedAlgHom.comp_assoc, f.comp_baseMap]⟩
  map_id _ := Domain.Inclusion.ext rfl
  map_comp _ _ := Domain.Inclusion.ext rfl

@[simp]
theorem extendDomainFunctor_map_restriction (i j : a.Index)
    (h : Set.range (a.chart i) ⊆ Set.range (a.chart j))
    {U V : Domain K (a.algebra i)} (f : U ⟶ V) :
    ((a.extendDomainFunctor i j h).map f).restriction = f.restriction := rfl

/-- Uniqueness for all bounded affinoid test maps recovers the inner base
equation from the equation over the containing chart. -/
def fullyFaithfulExtendDomain (i j : a.Index)
    (h : Set.range (a.chart i) ⊆ Set.range (a.chart j)) :
    (a.extendDomainFunctor i j h).FullyFaithful where
  preimage {U V} f := ⟨f.restriction, by
    apply a.restriction_hom_ext i j h U.algebra
    exact f.comp_baseMap⟩
  map_preimage _ := Domain.Inclusion.ext rfl
  preimage_map _ := Domain.Inclusion.ext rfl

instance (i j : a.Index)
    (h : Set.range (a.chart i) ⊆ Set.range (a.chart j)) :
    (a.extendDomainFunctor i j h).Full :=
  (a.fullyFaithfulExtendDomain i j h).full

instance (i j : a.Index)
    (h : Set.range (a.chart i) ⊆ Set.range (a.chart j)) :
    (a.extendDomainFunctor i j h).Faithful :=
  (a.fullyFaithfulExtendDomain i j h).faithful

theorem extendDomainFunctor_comp_toAffinoidSpace (i j : a.Index)
    (h : Set.range (a.chart i) ⊆ Set.range (a.chart j)) :
    a.extendDomainFunctor i j h ⋙ Domain.toAffinoidSpace K (a.algebra j) =
      Domain.toAffinoidSpace K (a.algebra i) := rfl

theorem extendDomainFunctor_comp_toTopologicalSpace (i j : a.Index)
    (h : Set.range (a.chart i) ⊆ Set.range (a.chart j)) :
    a.extendDomainFunctor i j h ⋙ Domain.toTopologicalSpace K (a.algebra j) =
      Domain.toTopologicalSpace K (a.algebra i) := rfl

/-- Self-containment extension is naturally the identity; both comparison
maps are the identity on the unchanged represented algebra. -/
def extendDomainSelfIso (i : a.Index)
    (h : Set.range (a.chart i) ⊆ Set.range (a.chart i)) :
    a.extendDomainFunctor i i h ≅ 𝟭 (Domain K (a.algebra i)) :=
  NatIso.ofComponents (fun U => {
    hom := ⟨BoundedAlgHom.id K U.algebra, by
      change U.baseMap = U.baseMap.comp (a.restriction i i h)
      rw [a.restriction_id, BoundedAlgHom.comp_id]⟩
    inv := ⟨BoundedAlgHom.id K U.algebra, by
      change U.baseMap.comp (a.restriction i i h) = U.baseMap
      rw [a.restriction_id, BoundedAlgHom.comp_id]⟩
    hom_inv_id := Domain.Inclusion.ext rfl
    inv_hom_id := Domain.Inclusion.ext rfl }) (by
      intro U V f
      apply Domain.Inclusion.ext
      rfl)

/-- Nested original chart containments agree with direct extension. Both
comparison restrictions are bounded identities, using the original atlas
composition equation rather than equality inferred from spectrum points. -/
def extendDomainCompIso (i j k : a.Index)
    (hij : Set.range (a.chart i) ⊆ Set.range (a.chart j))
    (hjk : Set.range (a.chart j) ⊆ Set.range (a.chart k))
    (hik : Set.range (a.chart i) ⊆ Set.range (a.chart k)) :
    a.extendDomainFunctor i j hij ⋙ a.extendDomainFunctor j k hjk ≅
      a.extendDomainFunctor i k hik :=
  NatIso.ofComponents (fun U => {
    hom := ⟨BoundedAlgHom.id K U.algebra, by
      change U.baseMap.comp (a.restriction i k hik) =
        (U.baseMap.comp (a.restriction i j hij)).comp (a.restriction j k hjk)
      rw [a.restriction_comp i j k hij hjk hik, BoundedAlgHom.comp_assoc]⟩
    inv := ⟨BoundedAlgHom.id K U.algebra, by
      change (U.baseMap.comp (a.restriction i j hij)).comp (a.restriction j k hjk) =
        U.baseMap.comp (a.restriction i k hik)
      rw [a.restriction_comp i j k hij hjk hik, BoundedAlgHom.comp_assoc]⟩
    hom_inv_id := Domain.Inclusion.ext rfl
    inv_hom_id := Domain.Inclusion.ext rfl }) (by
      intro U V f
      apply Domain.Inclusion.ext
      rfl)

@[simp]
theorem extendDomainCompIso_hom_restriction (i j k : a.Index)
    (hij : Set.range (a.chart i) ⊆ Set.range (a.chart j))
    (hjk : Set.range (a.chart j) ⊆ Set.range (a.chart k))
    (hik : Set.range (a.chart i) ⊆ Set.range (a.chart k))
    (U : Domain K (a.algebra i)) :
    ((a.extendDomainCompIso i j k hij hjk hik).hom.app U).restriction =
      BoundedAlgHom.id K U.algebra := rfl

theorem extendDomain_self_locus (i : a.Index)
    (h : Set.range (a.chart i) ⊆ Set.range (a.chart i))
    (U : Domain K (a.algebra i)) :
    (a.extendDomain i i h U).locus = U.locus :=
  Domain.locus_eq_of_iso ((a.extendDomainSelfIso i h).app U)

theorem extendDomain_comp_locus (i j k : a.Index)
    (hij : Set.range (a.chart i) ⊆ Set.range (a.chart j))
    (hjk : Set.range (a.chart j) ⊆ Set.range (a.chart k))
    (hik : Set.range (a.chart i) ⊆ Set.range (a.chart k))
    (U : Domain K (a.algebra i)) :
    (a.extendDomain j k hjk (a.extendDomain i j hij U)).locus =
      (a.extendDomain i k hik U).locus :=
  Domain.locus_eq_of_iso ((a.extendDomainCompIso i j k hij hjk hik).app U)

end Langlands.Analytic.IndexedAffinoidAtlas
