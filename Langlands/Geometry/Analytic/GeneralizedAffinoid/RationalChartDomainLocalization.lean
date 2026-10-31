import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartDomainComposition
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Equivalence

/-! # Localizing full domains at an actual rational chart -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : PresentedAffinoidAlgebra K}

omit [CompleteSpace K] in
private theorem spectrum_comp {B C : PresentedAffinoidAlgebra K}
    (i : BoundedAlgHom K A B) (j : BoundedAlgHom K B C) (x : BanachSpectrum C) :
    BanachSpectrum.comap (j.comp i).toBoundedRingHom x =
      BanachSpectrum.comap i.toBoundedRingHom
        (BanachSpectrum.comap j.toBoundedRingHom x) := by
  apply BanachSpectrum.ext
  intro a
  rfl

/-- An actual ambient domain inclusion into the rational chart represents
its inverse-image locus over the chart quotient. -/
theorem represents_restriction (d : RationalChart K A) (V : Domain K A)
    (f : V ⟶ d.toDomain) :
    Represents K f.restriction (d.spectrumMap ⁻¹' V.locus) := by
  let j : BoundedAlgHom K d.algebra V.algebra := f.restriction
  have hj : j.comp d.baseMap = V.baseMap := f.comp_baseMap
  change Represents K j (d.spectrumMap ⁻¹' V.locus)
  have hspec (y : BanachSpectrum V.algebra) :
      d.spectrumMap (BanachSpectrum.comap j.toBoundedRingHom y) =
        V.spectrumMap y := f.spectrumMap_over_base y
  refine ⟨V.represents.1.preimage d.spectrumMap.continuous, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨y, rfl⟩
      change d.spectrumMap (BanachSpectrum.comap j.toBoundedRingHom y) ∈
        V.locus
      rw [hspec]
      exact V.represents.hasImageIn y
    · intro hx
      change d.spectrumMap x ∈ V.locus at hx
      obtain ⟨y, hy⟩ := V.represents.2.1.symm ▸ hx
      exact ⟨y, d.spectrumMap_injective ((hspec y).trans hy)⟩
  · intro R φ hφ
    have hφ' : HasImageIn K (φ.comp d.baseMap) V.locus := by
      intro x
      rw [spectrum_comp]
      exact hφ x
    obtain ⟨θ, hθ, huniq⟩ := V.represents.2.2 R (φ.comp d.baseMap) hφ'
    refine ⟨θ, ?_, ?_⟩
    · apply RationalPresentation.hom_ext_base K A d.radii d.denominator d.numerators
        R d.generates
      change (θ.comp j).comp d.baseMap = φ.comp d.baseMap
      rw [BoundedAlgHom.comp_assoc, hj, hθ]
    · intro θ' hθ'
      apply huniq θ'
      rw [← hj, ← BoundedAlgHom.comp_assoc, hθ']

/-- Restriction retains the actual ambient domain algebra and uses the
stored bounded restriction as its structural map over the chart quotient. -/
def restrictDomain (d : RationalChart K A) (V : Domain K A) (f : V ⟶ d.toDomain) :
    Domain K d.algebra where
  algebra := V.algebra
  baseMap := f.restriction
  locus := d.spectrumMap ⁻¹' V.locus
  represents := d.represents_restriction V f

@[simp] theorem restrictDomain_algebra (d : RationalChart K A) (V : Domain K A)
    (f : V ⟶ d.toDomain) : (d.restrictDomain V f).algebra = V.algebra := rfl

@[simp] theorem restrictDomain_baseMap (d : RationalChart K A) (V : Domain K A)
    (f : V ⟶ d.toDomain) : (d.restrictDomain V f).baseMap = f.restriction := rfl

@[simp] theorem restrictDomain_locus (d : RationalChart K A) (V : Domain K A)
    (f : V ⟶ d.toDomain) :
    (d.restrictDomain V f).locus = d.spectrumMap ⁻¹' V.locus := rfl

theorem restrictDomain_baseMap_comp (d : RationalChart K A) (V : Domain K A)
    (f : V ⟶ d.toDomain) :
    (d.restrictDomain V f).baseMap.comp d.baseMap = V.baseMap := f.comp_baseMap

/-- Locus containment alone constructs the needed bounded inclusion by the
proved full domain universal property. -/
def restrictDomainOfSubset (d : RationalChart K A) (V : Domain K A)
    (h : V.locus ⊆ d.locus) : Domain K d.algebra :=
  d.restrictDomain V (Domain.inclusionOfSubset V d.toDomain h)

@[simp] theorem restrictDomainOfSubset_algebra (d : RationalChart K A) (V : Domain K A)
    (h : V.locus ⊆ d.locus) : (d.restrictDomainOfSubset V h).algebra = V.algebra := rfl

@[simp] theorem restrictDomainOfSubset_locus (d : RationalChart K A) (V : Domain K A)
    (h : V.locus ⊆ d.locus) :
    (d.restrictDomainOfSubset V h).locus = d.spectrumMap ⁻¹' V.locus := rfl

/-- Compose an inner domain with the rational chart, keeping its actual
bounded inclusion into that chart as part of the object. -/
def extendDomainOverFunctor (d : RationalChart K A) :
    Domain K d.algebra ⥤ Over d.toDomain where
  obj U := Over.mk (d.extendDomainInclusion U)
  map {U V} f := Over.homMk (d.extendDomainFunctor.map f) (by
    apply Domain.Inclusion.ext
    exact f.comp_baseMap)
  map_id _ := by apply Over.OverMorphism.ext; apply Domain.Inclusion.ext; rfl
  map_comp _ _ := by apply Over.OverMorphism.ext; apply Domain.Inclusion.ext; rfl

/-- A commuting triangle of actual ambient inclusions is exactly the base
map equation needed after restriction to the rational quotient. -/
def restrictDomainFunctor (d : RationalChart K A) :
    Over d.toDomain ⥤ Domain K d.algebra where
  obj V := d.restrictDomain V.left V.hom
  map f := ⟨f.left.restriction, congrArg Domain.Inclusion.restriction f.w⟩
  map_id _ := Domain.Inclusion.ext rfl
  map_comp _ _ := Domain.Inclusion.ext rfl

@[simp] theorem extendDomainOverFunctor_map_restriction (d : RationalChart K A)
    {U V : Domain K d.algebra} (f : U ⟶ V) :
    ((d.extendDomainOverFunctor.map f).left).restriction = f.restriction := rfl

@[simp] theorem restrictDomainFunctor_map_restriction (d : RationalChart K A)
    {U V : Over d.toDomain} (f : U ⟶ V) :
    (d.restrictDomainFunctor.map f).restriction = f.left.restriction := rfl

/-- The inner round trip has identity bounded restrictions on the unchanged
algebra in both directions. -/
def restrictExtendDomainIso (d : RationalChart K A) (U : Domain K d.algebra) :
    d.restrictDomain (d.extendDomain U) (d.extendDomainInclusion U) ≅ U where
  hom := ⟨BoundedAlgHom.id K U.algebra, rfl⟩
  inv := ⟨BoundedAlgHom.id K U.algebra, rfl⟩
  hom_inv_id := Domain.Inclusion.ext rfl
  inv_hom_id := Domain.Inclusion.ext rfl

/-- The ambient round trip also has identity bounded restrictions. Its base
map equations are the equation already stored by the actual inclusion. -/
def extendRestrictDomainIso (d : RationalChart K A) (V : Domain K A)
    (f : V ⟶ d.toDomain) : d.extendDomain (d.restrictDomain V f) ≅ V where
  hom := ⟨BoundedAlgHom.id K V.algebra, by
    change V.baseMap = f.restriction.comp d.baseMap
    exact f.comp_baseMap.symm⟩
  inv := ⟨BoundedAlgHom.id K V.algebra, by
    change f.restriction.comp d.baseMap = V.baseMap
    exact f.comp_baseMap⟩
  hom_inv_id := Domain.Inclusion.ext rfl
  inv_hom_id := Domain.Inclusion.ext rfl

@[simp] theorem restrictExtendDomainIso_hom_restriction (d : RationalChart K A)
    (U : Domain K d.algebra) :
    (d.restrictExtendDomainIso U).hom.restriction = BoundedAlgHom.id K U.algebra := rfl

@[simp] theorem restrictExtendDomainIso_inv_restriction (d : RationalChart K A)
    (U : Domain K d.algebra) :
    (d.restrictExtendDomainIso U).inv.restriction = BoundedAlgHom.id K U.algebra := rfl

@[simp] theorem extendRestrictDomainIso_hom_restriction (d : RationalChart K A)
    (V : Domain K A) (f : V ⟶ d.toDomain) :
    (d.extendRestrictDomainIso V f).hom.restriction = BoundedAlgHom.id K V.algebra := rfl

@[simp] theorem extendRestrictDomainIso_inv_restriction (d : RationalChart K A)
    (V : Domain K A) (f : V ⟶ d.toDomain) :
    (d.extendRestrictDomainIso V f).inv.restriction = BoundedAlgHom.id K V.algebra := rfl

theorem restrict_extendDomain_locus (d : RationalChart K A) (U : Domain K d.algebra) :
    (d.restrictDomain (d.extendDomain U) (d.extendDomainInclusion U)).locus = U.locus :=
  Domain.locus_eq_of_iso (d.restrictExtendDomainIso U)

theorem extend_restrictDomain_locus (d : RationalChart K A) (V : Domain K A)
    (f : V ⟶ d.toDomain) :
    (d.extendDomain (d.restrictDomain V f)).locus = V.locus :=
  Domain.locus_eq_of_iso (d.extendRestrictDomainIso V f)

/-- Full domains over the actual rational quotient are equivalent to actual
ambient full domains equipped with an inclusion into that rational chart. -/
def domainLocalizationEquivalence (d : RationalChart K A) :
    Domain K d.algebra ≌ Over d.toDomain where
  functor := d.extendDomainOverFunctor
  inverse := d.restrictDomainFunctor
  unitIso := NatIso.ofComponents (fun U => (d.restrictExtendDomainIso U).symm)
    (by intro U V f; apply Domain.Inclusion.ext; rfl)
  counitIso := NatIso.ofComponents (fun V =>
    Over.isoMk (d.extendRestrictDomainIso V.left V.hom) (by
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

/-- Forgetting the inclusion recovers the actual extension functor. -/
theorem extendDomainOverFunctor_comp_forget (d : RationalChart K A) :
    d.extendDomainOverFunctor ⋙ Over.forget d.toDomain = d.extendDomainFunctor := rfl

/-- Restriction retains the actual ambient represented algebra and arrows. -/
theorem restrictDomainFunctor_comp_toAffinoidSpace (d : RationalChart K A) :
    d.restrictDomainFunctor ⋙ Domain.toAffinoidSpace K d.algebra =
      Over.forget d.toDomain ⋙ Domain.toAffinoidSpace K A := rfl

theorem restrictDomainFunctor_comp_toTopologicalSpace (d : RationalChart K A) :
    d.restrictDomainFunctor ⋙ Domain.toTopologicalSpace K d.algebra =
      Over.forget d.toDomain ⋙ Domain.toTopologicalSpace K A := rfl

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart
