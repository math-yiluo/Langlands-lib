import Langlands.Geometry.Analytic.AtlasAffinoidDomainExtension
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Equivalence

/-! # Full affinoid-domain localization at original atlas chart containments -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas

open CategoryTheory PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)
  (i j : a.Index) (h : Set.range (a.chart i) ⊆ Set.range (a.chart j))

/-- An actual full-domain inclusion into the original relative chart domain
represents the inverse-image locus over the smaller chart's algebra. -/
theorem represents_domainRestriction (V : Domain K (a.algebra j))
    (f : V ⟶ a.restrictionDomain i j h) :
    Represents K f.restriction
      ((a.restrictionDomain i j h).spectrumMap ⁻¹' V.locus) := by
  let r : BoundedAlgHom K (a.algebra j) (a.algebra i) := a.restriction i j h
  let q : BoundedAlgHom K (a.algebra i) V.algebra := f.restriction
  have hq : q.comp r = V.baseMap := f.comp_baseMap
  change Represents K q ((a.restrictionDomain i j h).spectrumMap ⁻¹' V.locus)
  have hspec (y : BanachSpectrum V.algebra) :
      (a.restrictionDomain i j h).spectrumMap
          (BanachSpectrum.comap q.toBoundedRingHom y) =
        V.spectrumMap y := f.spectrumMap_over_base y
  refine ⟨V.represents.1.preimage (a.restrictionDomain i j h).spectrumMap.continuous,
    ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨y, rfl⟩
      change (a.restrictionDomain i j h).spectrumMap
        (BanachSpectrum.comap q.toBoundedRingHom y) ∈ V.locus
      rw [hspec]
      exact V.represents.hasImageIn y
    · intro hx
      change (a.restrictionDomain i j h).spectrumMap x ∈ V.locus at hx
      obtain ⟨y, hy⟩ := V.represents.2.1.symm ▸ hx
      exact ⟨y, (a.isEmbedding_restriction i j h).injective ((hspec y).trans hy)⟩
  · intro R φ hφ
    have hφ' : HasImageIn K (φ.comp r) V.locus := by
      intro x
      change (a.restrictionDomain i j h).spectrumMap
        (BanachSpectrum.comap φ.toBoundedRingHom x) ∈ V.locus
      exact hφ x
    obtain ⟨θ, hθ, huniq⟩ := V.represents.2.2 R (φ.comp r) hφ'
    refine ⟨θ, ?_, ?_⟩
    · apply a.restriction_hom_ext i j h R
      change (θ.comp q).comp r = φ.comp r
      rw [BoundedAlgHom.comp_assoc, hq, hθ]
    · intro θ' hθ'
      apply huniq θ'
      rw [← hq, ← BoundedAlgHom.comp_assoc, hθ']

/-- Restriction keeps the actual represented algebra and uses the supplied
actual bounded inclusion as its structural map over the smaller chart. -/
def restrictDomain (V : Domain K (a.algebra j))
    (f : V ⟶ a.restrictionDomain i j h) : Domain K (a.algebra i) where
  algebra := V.algebra
  baseMap := f.restriction
  locus := (a.restrictionDomain i j h).spectrumMap ⁻¹' V.locus
  represents := a.represents_domainRestriction i j h V f

@[simp]
theorem restrictDomain_algebra (V : Domain K (a.algebra j))
    (f : V ⟶ a.restrictionDomain i j h) :
    (a.restrictDomain i j h V f).algebra = V.algebra := rfl

@[simp]
theorem restrictDomain_baseMap (V : Domain K (a.algebra j))
    (f : V ⟶ a.restrictionDomain i j h) :
    (a.restrictDomain i j h V f).baseMap = f.restriction := rfl

@[simp]
theorem restrictDomain_locus (V : Domain K (a.algebra j))
    (f : V ⟶ a.restrictionDomain i j h) :
    (a.restrictDomain i j h V f).locus =
      (a.restrictionDomain i j h).spectrumMap ⁻¹' V.locus := rfl

theorem restrictDomain_baseMap_comp (V : Domain K (a.algebra j))
    (f : V ⟶ a.restrictionDomain i j h) :
    (a.restrictDomain i j h V f).baseMap.comp (a.restriction i j h) =
      V.baseMap := f.comp_baseMap

/-- Containment of the actual loci constructs the needed inclusion by the
full affinoid-test universal property. -/
def restrictDomainOfSubset (V : Domain K (a.algebra j))
    (hV : V.locus ⊆ (a.restrictionDomain i j h).locus) :
    Domain K (a.algebra i) :=
  a.restrictDomain i j h V
    (Domain.inclusionOfSubset V (a.restrictionDomain i j h) hV)

@[simp]
theorem restrictDomainOfSubset_algebra (V : Domain K (a.algebra j))
    (hV : V.locus ⊆ (a.restrictionDomain i j h).locus) :
    (a.restrictDomainOfSubset i j h V hV).algebra = V.algebra := rfl

@[simp]
theorem restrictDomainOfSubset_locus (V : Domain K (a.algebra j))
    (hV : V.locus ⊆ (a.restrictionDomain i j h).locus) :
    (a.restrictDomainOfSubset i j h V hV).locus =
      (a.restrictionDomain i j h).spectrumMap ⁻¹' V.locus := rfl

/-- Extension stores the actual inclusion into the original relative chart. -/
def extendDomainOverFunctor :
    Domain K (a.algebra i) ⥤ Over (a.restrictionDomain i j h) where
  obj U := Over.mk (a.extendDomainInclusion i j h U)
  map {U V} f := Over.homMk ((a.extendDomainFunctor i j h).map f) (by
    apply Domain.Inclusion.ext
    exact f.comp_baseMap)
  map_id _ := by apply Over.OverMorphism.ext; apply Domain.Inclusion.ext; rfl
  map_comp _ _ := by apply Over.OverMorphism.ext; apply Domain.Inclusion.ext; rfl

/-- An actual commuting triangle over the relative chart gives exactly the
bounded base equation needed after restriction. -/
def restrictDomainFunctor :
    Over (a.restrictionDomain i j h) ⥤ Domain K (a.algebra i) where
  obj V := a.restrictDomain i j h V.left V.hom
  map f := ⟨f.left.restriction, congrArg Domain.Inclusion.restriction f.w⟩
  map_id _ := Domain.Inclusion.ext rfl
  map_comp _ _ := Domain.Inclusion.ext rfl

@[simp]
theorem extendDomainOverFunctor_map_restriction
    {U V : Domain K (a.algebra i)} (f : U ⟶ V) :
    ((a.extendDomainOverFunctor i j h).map f).left.restriction =
      f.restriction := rfl

@[simp]
theorem restrictDomainFunctor_map_restriction
    {U V : Over (a.restrictionDomain i j h)} (f : U ⟶ V) :
    ((a.restrictDomainFunctor i j h).map f).restriction = f.left.restriction := rfl

/-- The inner round trip has identity bounded maps on the actual unchanged
represented algebra. -/
def restrictExtendDomainIso (U : Domain K (a.algebra i)) :
    a.restrictDomain i j h (a.extendDomain i j h U)
      (a.extendDomainInclusion i j h U) ≅ U where
  hom := ⟨BoundedAlgHom.id K U.algebra, rfl⟩
  inv := ⟨BoundedAlgHom.id K U.algebra, rfl⟩
  hom_inv_id := Domain.Inclusion.ext rfl
  inv_hom_id := Domain.Inclusion.ext rfl

/-- The ambient round trip also has identity bounded maps; its base equations
are the equation stored by the actual inclusion. -/
def extendRestrictDomainIso (V : Domain K (a.algebra j))
    (f : V ⟶ a.restrictionDomain i j h) :
    a.extendDomain i j h (a.restrictDomain i j h V f) ≅ V where
  hom := ⟨BoundedAlgHom.id K V.algebra, by
    change V.baseMap = f.restriction.comp (a.restriction i j h)
    exact f.comp_baseMap.symm⟩
  inv := ⟨BoundedAlgHom.id K V.algebra, by
    change f.restriction.comp (a.restriction i j h) = V.baseMap
    exact f.comp_baseMap⟩
  hom_inv_id := Domain.Inclusion.ext rfl
  inv_hom_id := Domain.Inclusion.ext rfl

@[simp]
theorem restrictExtendDomainIso_hom_restriction (U : Domain K (a.algebra i)) :
    (a.restrictExtendDomainIso i j h U).hom.restriction =
      BoundedAlgHom.id K U.algebra := rfl

@[simp]
theorem restrictExtendDomainIso_inv_restriction (U : Domain K (a.algebra i)) :
    (a.restrictExtendDomainIso i j h U).inv.restriction =
      BoundedAlgHom.id K U.algebra := rfl

@[simp]
theorem extendRestrictDomainIso_hom_restriction (V : Domain K (a.algebra j))
    (f : V ⟶ a.restrictionDomain i j h) :
    (a.extendRestrictDomainIso i j h V f).hom.restriction =
      BoundedAlgHom.id K V.algebra := rfl

@[simp]
theorem extendRestrictDomainIso_inv_restriction (V : Domain K (a.algebra j))
    (f : V ⟶ a.restrictionDomain i j h) :
    (a.extendRestrictDomainIso i j h V f).inv.restriction =
      BoundedAlgHom.id K V.algebra := rfl

theorem restrict_extendDomain_locus (U : Domain K (a.algebra i)) :
    (a.restrictDomain i j h (a.extendDomain i j h U)
      (a.extendDomainInclusion i j h U)).locus = U.locus :=
  Domain.locus_eq_of_iso (a.restrictExtendDomainIso i j h U)

theorem extend_restrictDomain_locus (V : Domain K (a.algebra j))
    (f : V ⟶ a.restrictionDomain i j h) :
    (a.extendDomain i j h (a.restrictDomain i j h V f)).locus = V.locus :=
  Domain.locus_eq_of_iso (a.extendRestrictDomainIso i j h V f)

/-- Full domains over the smaller original chart are equivalent to actual
full domains over the containing chart equipped with an inclusion into the
original relative chart domain. -/
def domainLocalizationEquivalence :
    Domain K (a.algebra i) ≌ Over (a.restrictionDomain i j h) where
  functor := a.extendDomainOverFunctor i j h
  inverse := a.restrictDomainFunctor i j h
  unitIso := NatIso.ofComponents (fun U => (a.restrictExtendDomainIso i j h U).symm)
    (by intro U V f; apply Domain.Inclusion.ext; rfl)
  counitIso := NatIso.ofComponents (fun V =>
    Over.isoMk (a.extendRestrictDomainIso i j h V.left V.hom) (by
      apply Domain.Inclusion.ext
      rfl)) (by
    intro U V f
    apply Over.OverMorphism.ext
    apply Domain.Inclusion.ext
    rfl)
  functor_unitIso_comp U := by
    apply Over.OverMorphism.ext
    apply Domain.Inclusion.ext
    rfl

/-- Forgetting the inclusion recovers extension of the actual domains. -/
theorem extendDomainOverFunctor_comp_forget :
    a.extendDomainOverFunctor i j h ⋙ Over.forget (a.restrictionDomain i j h) =
      a.extendDomainFunctor i j h := rfl

/-- Restriction retains the actual represented algebra and arrows. -/
theorem restrictDomainFunctor_comp_toAffinoidSpace :
    a.restrictDomainFunctor i j h ⋙ Domain.toAffinoidSpace K (a.algebra i) =
      Over.forget (a.restrictionDomain i j h) ⋙
        Domain.toAffinoidSpace K (a.algebra j) := rfl

theorem restrictDomainFunctor_comp_toTopologicalSpace :
    a.restrictDomainFunctor i j h ⋙ Domain.toTopologicalSpace K (a.algebra i) =
      Over.forget (a.restrictionDomain i j h) ⋙
        Domain.toTopologicalSpace K (a.algebra j) := rfl

end Langlands.Analytic.IndexedAffinoidAtlas
