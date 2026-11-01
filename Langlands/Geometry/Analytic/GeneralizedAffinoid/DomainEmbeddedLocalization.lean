import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainRelativeRepresentation
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartDomainComposition
import Mathlib.CategoryTheory.Equivalence

/-! # Full-domain localization along a specified embedded domain -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.Domain

open CategoryTheory Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : PresentedAffinoidAlgebra K}
  (U : Domain K A) (hU : Function.Injective U.spectrumMap)

/-- Extend a full domain along a particular domain with injective structural
spectrum map. The actual algebra is retained and its base map is composed. -/
def extendOfInjective (V : Domain K U.algebra) : Domain K A where
  algebra := V.algebra
  baseMap := V.baseMap.comp U.baseMap
  locus := U.spectrumMap '' V.locus
  represents := U.represents.comp_of_injective V.represents hU

@[simp]
theorem extendOfInjective_algebra (V : Domain K U.algebra) :
    (U.extendOfInjective hU V).algebra = V.algebra := rfl

@[simp]
theorem extendOfInjective_baseMap (V : Domain K U.algebra) :
    (U.extendOfInjective hU V).baseMap = V.baseMap.comp U.baseMap := rfl

@[simp]
theorem extendOfInjective_locus (V : Domain K U.algebra) :
    (U.extendOfInjective hU V).locus = U.spectrumMap '' V.locus := rfl

theorem extendOfInjective_locus_subset (V : Domain K U.algebra) :
    (U.extendOfInjective hU V).locus ⊆ U.locus := by
  rintro _ ⟨x, _, rfl⟩
  exact U.represents.hasImageIn x

theorem extendOfInjective_spectrumMap (V : Domain K U.algebra)
    (x : BanachSpectrum V.algebra) :
    (U.extendOfInjective hU V).spectrumMap x = U.spectrumMap (V.spectrumMap x) := by
  apply BanachSpectrum.ext
  intro a
  rfl

/-- The inclusion into the containing domain stores exactly the inner
domain's bounded structural map. -/
def extendOfInjectiveInclusion (V : Domain K U.algebra) :
    U.extendOfInjective hU V ⟶ U where
  restriction := V.baseMap
  comp_baseMap := rfl

@[simp]
theorem extendOfInjectiveInclusion_restriction (V : Domain K U.algebra) :
    (U.extendOfInjectiveInclusion hU V).restriction = V.baseMap := rfl

/-- Extension retains actual bounded restrictions between inner domains. -/
def extendOfInjectiveFunctor : Domain K U.algebra ⥤ Domain K A where
  obj := U.extendOfInjective hU
  map {V W} f := ⟨f.restriction, by
    change f.restriction.comp (W.baseMap.comp U.baseMap) = V.baseMap.comp U.baseMap
    rw [← BoundedAlgHom.comp_assoc, f.comp_baseMap]⟩
  map_id _ := Inclusion.ext rfl
  map_comp _ _ := Inclusion.ext rfl

@[simp]
theorem extendOfInjectiveFunctor_map_restriction
    {V W : Domain K U.algebra} (f : V ⟶ W) :
    ((U.extendOfInjectiveFunctor hU).map f).restriction = f.restriction := rfl

/-- Full test-map cancellation recovers the equation over the inner base
from the bounded equation over the ambient base. -/
def fullyFaithfulExtendOfInjective :
    (U.extendOfInjectiveFunctor hU).FullyFaithful where
  preimage {V W} f := ⟨f.restriction, by
    apply U.represents.hom_ext V.algebra
    exact f.comp_baseMap⟩
  map_preimage _ := Inclusion.ext rfl
  preimage_map _ := Inclusion.ext rfl

instance : (U.extendOfInjectiveFunctor hU).Full :=
  (U.fullyFaithfulExtendOfInjective hU).full

instance : (U.extendOfInjectiveFunctor hU).Faithful :=
  (U.fullyFaithfulExtendOfInjective hU).faithful

theorem extendOfInjectiveFunctor_comp_toAffinoidSpace :
    U.extendOfInjectiveFunctor hU ⋙ toAffinoidSpace K A =
      toAffinoidSpace K U.algebra := rfl

theorem extendOfInjectiveFunctor_comp_toTopologicalSpace :
    U.extendOfInjectiveFunctor hU ⋙ toTopologicalSpace K A =
      toTopologicalSpace K U.algebra := rfl

/-- Extension retains the actual inclusion into the containing domain. -/
def extendOfInjectiveOverFunctor : Domain K U.algebra ⥤ Over U where
  obj V := Over.mk (U.extendOfInjectiveInclusion hU V)
  map f := Over.homMk ((U.extendOfInjectiveFunctor hU).map f) (by
    apply Inclusion.ext
    exact f.comp_baseMap)
  map_id _ := by apply Over.OverMorphism.ext; apply Inclusion.ext; rfl
  map_comp _ _ := by apply Over.OverMorphism.ext; apply Inclusion.ext; rfl

@[simp]
theorem extendOfInjectiveOverFunctor_map_restriction
    {V W : Domain K U.algebra} (f : V ⟶ W) :
    ((U.extendOfInjectiveOverFunctor hU).map f).left.restriction =
      f.restriction := rfl

theorem extendOfInjectiveOverFunctor_comp_forget :
    U.extendOfInjectiveOverFunctor hU ⋙ Over.forget U =
      U.extendOfInjectiveFunctor hU := rfl

/-- The inner round trip uses identity bounded maps on the unchanged algebra. -/
def relativeExtendOfInjectiveIso (V : Domain K U.algebra) :
    U.relative (U.extendOfInjective hU V)
      (U.extendOfInjectiveInclusion hU V) ≅ V where
  hom := ⟨BoundedAlgHom.id K V.algebra, rfl⟩
  inv := ⟨BoundedAlgHom.id K V.algebra, rfl⟩
  hom_inv_id := Inclusion.ext rfl
  inv_hom_id := Inclusion.ext rfl

/-- The ambient round trip also retains its algebra. The comparison maps
use the original inclusion's full bounded base equation. -/
def extendRelativeOfInjectiveIso (V : Domain K A) (f : V ⟶ U) :
    U.extendOfInjective hU (U.relative V f) ≅ V where
  hom := ⟨BoundedAlgHom.id K V.algebra, by
    change V.baseMap = f.restriction.comp U.baseMap
    exact f.comp_baseMap.symm⟩
  inv := ⟨BoundedAlgHom.id K V.algebra, by
    change f.restriction.comp U.baseMap = V.baseMap
    exact f.comp_baseMap⟩
  hom_inv_id := Inclusion.ext rfl
  inv_hom_id := Inclusion.ext rfl

@[simp]
theorem relativeExtendOfInjectiveIso_hom_restriction (V : Domain K U.algebra) :
    (U.relativeExtendOfInjectiveIso hU V).hom.restriction =
      BoundedAlgHom.id K V.algebra := rfl

@[simp]
theorem relativeExtendOfInjectiveIso_inv_restriction (V : Domain K U.algebra) :
    (U.relativeExtendOfInjectiveIso hU V).inv.restriction =
      BoundedAlgHom.id K V.algebra := rfl

@[simp]
theorem extendRelativeOfInjectiveIso_hom_restriction
    (V : Domain K A) (f : V ⟶ U) :
    (U.extendRelativeOfInjectiveIso hU V f).hom.restriction =
      BoundedAlgHom.id K V.algebra := rfl

@[simp]
theorem extendRelativeOfInjectiveIso_inv_restriction
    (V : Domain K A) (f : V ⟶ U) :
    (U.extendRelativeOfInjectiveIso hU V f).inv.restriction =
      BoundedAlgHom.id K V.algebra := rfl

theorem relative_extendOfInjective_locus (V : Domain K U.algebra) :
    (U.relative (U.extendOfInjective hU V)
      (U.extendOfInjectiveInclusion hU V)).locus = V.locus :=
  locus_eq_of_iso (U.relativeExtendOfInjectiveIso hU V)

theorem extendOfInjective_relative_locus (V : Domain K A) (f : V ⟶ U) :
    (U.extendOfInjective hU (U.relative V f)).locus = V.locus :=
  locus_eq_of_iso (U.extendRelativeOfInjectiveIso hU V f)

/-- Full domains over the actual algebra of a specified embedded domain
are equivalent to ambient full domains with their actual inclusion into it.
The inverse is the relative functor, which itself needs no injectivity. -/
def localizationEquivalenceOfInjective : Domain K U.algebra ≌ Over U where
  functor := U.extendOfInjectiveOverFunctor hU
  inverse := U.relativeFunctor
  unitIso := NatIso.ofComponents
    (fun V => (U.relativeExtendOfInjectiveIso hU V).symm)
    (by intro V W f; apply Inclusion.ext; rfl)
  counitIso := NatIso.ofComponents
    (fun V => Over.isoMk (U.extendRelativeOfInjectiveIso hU V.left V.hom) (by
      apply Inclusion.ext
      rfl))
    (by
      intro V W f
      apply Over.OverMorphism.ext
      apply Inclusion.ext
      rfl)
  functor_unitIso_comp V := by
    apply Over.OverMorphism.ext
    apply Inclusion.ext
    rfl

/-- The specified injectivity also gives the subspace topology on the
extended locus, without any injectivity input for the inner domain. -/
def extendOfInjectiveLocusHomeomorph (V : Domain K U.algebra) :
    V.locus ≃ₜ (U.extendOfInjective hU V).locus :=
  (U.spectrumMap.continuous.isClosedEmbedding hU).isEmbedding.homeomorphImage V.locus

@[simp]
theorem extendOfInjectiveLocusHomeomorph_apply_coe
    (V : Domain K U.algebra) (x : V.locus) :
    (U.extendOfInjectiveLocusHomeomorph hU V x : BanachSpectrum A) =
      U.spectrumMap x := rfl

/-- Embedded inner domains remain embedded after the actual extension. -/
theorem extendOfInjective_spectrumMap_injective (V : Domain K U.algebra)
    (hV : Function.Injective V.spectrumMap) :
    Function.Injective (U.extendOfInjective hU V).spectrumMap := by
  intro x y h
  apply hV
  apply hU
  exact (U.extendOfInjective_spectrumMap hU V x).symm.trans
    (h.trans (U.extendOfInjective_spectrumMap hU V y))

end Langlands.Analytic.PresentedAffinoidAlgebra.Domain
