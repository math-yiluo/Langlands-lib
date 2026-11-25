/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
public import WeilConjectures.CategoryTheory.Ringed.Sheaf.RingedSheafSliceAdjunction
public import WeilConjectures.CategoryTheory.Localized.LocalizedSheavesOverRepresentable
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import Mathlib.Algebra.Homology.QuasiIso
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.CategoryTheory.Ringed.RingedSectionLocalizationOfUniversesSupplement
public import WeilConjectures.CategoryTheory.RingedIdealGenerators
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import WeilConjectures.CategoryTheory.LocallyDerivedRingedIdealComplete
public import WeilConjectures.CategoryTheory.RingedDerivedRestriction
public import WeilConjectures.CategoryTheory.RingedSectionLocalization
public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.CategoryTheory.LocalCoefficientLocalization
public import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHom
public import Mathlib.CategoryTheory.Functor.OfSequence
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.CategoryTheory.ProperBaseChange.ElementSiteDescent
import WeilConjectures.CategoryTheory.ProperBaseChange.ContinuousCocontinuousRingedRestriction
import WeilConjectures.CategoryTheory.ProperBaseChange.ElementModulePresheafExtension

/-!
# Ringed presentation comparison data

Source: Stacks Project, Modules on Sites, Tag 03CR (equivalence case), and
Algebraization, Tag 099J (opening presentation reduction)
(blueprint: lem-weil-pbc-ringed-presentation-transport).

## Main definitions

- `RingedPresentationFunctor`: exactness, K-injectives, derived Hom and localization.
- `RingedPresentationEquivalence`: the two inverse module and derived functors.
- `RingedPresentationRestrictions`: sheaf slices and further restrictions.
- `RingedPresentationTransport`: the full comparison, tied to the specified morphism.

All derived categories below use the standard localization, with morphisms in universe
`u + 1`. This fixes a model of the unbounded derived category, without a smallness
assumption on its morphisms. The abbreviations expose precisely the existing definitions.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- The existing module category, with commutativity forgotten.
Source: Stacks 03CR (blueprint: lem-weil-pbc-ringed-presentation-transport). -/
abbrev PresentationModules {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) :=
  ringedSiteModules.{u} (localCoefficientRings R)

/-- The standard unbounded derived category of the recorded module category.
Source: Stacks 05RR (blueprint: lem-weil-pbc-ringed-presentation-transport). -/
abbrev PresentationDerived {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) :=
  letI := HasDerivedCategory.standard (PresentationModules R)
  DerivedCategory (PresentationModules R)

/-- The localization functor for the standard derived-category model.
Source: Stacks 05RR (blueprint: lem-weil-pbc-ringed-presentation-transport). -/
def presentationQ {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) :
    CochainComplex (PresentationModules R) ℤ ⥤ PresentationDerived R :=
  letI := HasDerivedCategory.standard (PresentationModules R)
  DerivedCategory.Q

/-- The existing derived internal Hom in the standard localization model.
Source: Stacks 08J7 (blueprint: lem-weil-pbc-ringed-presentation-transport). -/
def presentationRHom {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) :
    (PresentationDerived R)ᵒᵖ × PresentationDerived R ⥤ PresentationDerived R :=
  letI := HasDerivedCategory.standard (PresentationModules R)
  derivedInternalHomOfUniverses.{u, u, u, u + 1} J R

/-- The underlying sheaf of sets of a module sheaf.
Source: Stacks 03CR (blueprint: lem-weil-pbc-ringed-presentation-transport). -/
abbrev presentationForget {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) :=
  SheafOfModules.toSheaf (localCoefficientRings R) ⋙
    sheafCompose J (forget AddCommGrpCat.{u})

/-- Multiplication by an actual global ring section on the rank-one module.
Source: Stacks 0997 (blueprint: lem-weil-pbc-ringed-presentation-transport). -/
def presentationScalar {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (s : (R.obj ⋙ forget CommRingCat).sections) :
    SheafOfModules.unit (localCoefficientRings R) ⟶
      SheafOfModules.unit (localCoefficientRings R) where
  val := PresheafOfModules.sectionsSMul _ s

/-- Termwise application of an additive functor, with its instance made explicit.
Source: Stacks 05RR (blueprint: lem-weil-pbc-ringed-presentation-transport). -/
def presentationComplexMap {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    (F : PresentationModules R ⥤ PresentationModules S) (h : F.Additive) :
    CochainComplex (PresentationModules R) ℤ ⥤ CochainComplex (PresentationModules S) ℤ :=
  letI := h
  F.mapHomologicalComplex (ComplexShape.up ℤ)

/-- The exact termwise functor localized at quasi-isomorphisms; no resolution is chosen.
Source: Stacks 05RR (blueprint: lem-weil-pbc-ringed-presentation-transport). -/
def presentationDerivedMap {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    (F : PresentationModules R ⥤ PresentationModules S) (ha : F.Additive)
    (hl : PreservesFiniteLimits F) (hc : PreservesFiniteColimits F) :
    PresentationDerived R ⥤ PresentationDerived S :=
  letI := HasDerivedCategory.standard (PresentationModules R)
  letI := HasDerivedCategory.standard (PresentationModules S)
  letI := ha
  letI := hl
  letI := hc
  F.mapDerivedCategory

/-- The exact-functor, internal-Hom, K-injective and localization conclusions, for a
specified functor. The localization equation includes its canonical map from the ring.
The scalar comparison is an equality of multiplication maps, so imposes precisely the
transport of the chosen section, rather than an arbitrary choice of an inverted scalar.
Source: Stacks 03CR, 08JB and 0997
(blueprint: lem-weil-pbc-ringed-presentation-transport). -/
structure RingedPresentationFunctor
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (R : Sheaf J CommRingCat.{u}) (S : Sheaf K CommRingCat.{u})
    (F : PresentationModules R ⥤ PresentationModules S) where
  additive : F.Additive
  finiteLimits : PreservesFiniteLimits F
  finiteColimits : PreservesFiniteColimits F
  termwise : Nonempty (presentationQ R ⋙
    presentationDerivedMap F additive finiteLimits finiteColimits ≅
      presentationComplexMap F additive ⋙ presentationQ S)
  unit : F.obj (SheafOfModules.unit (localCoefficientRings R)) ≅
    SheafOfModules.unit (localCoefficientRings S)
  kInjective : ∀ I : CochainComplex (PresentationModules R) ℤ,
    I.IsKInjective → ((presentationComplexMap F additive).obj I).IsKInjective
  internalHom : Nonempty (presentationRHom R ⋙
    presentationDerivedMap F additive finiteLimits finiteColimits ≅
      ((presentationDerivedMap F additive finiteLimits finiteColimits).op.prod
        (presentationDerivedMap F additive finiteLimits finiteColimits)) ⋙ presentationRHom S)
  localization : ∀ (s : (R.obj ⋙ forget CommRingCat).sections)
    (t : (S.obj ⋙ forget CommRingCat).sections),
    F.map (presentationScalar R s) ≫ unit.hom = unit.hom ≫ presentationScalar S t →
    ∃ l : F.obj (ringedSectionLocalizationOfUniverses R s) ≅
      ringedSectionLocalizationOfUniverses S t,
      F.map (ringedSectionLocalizationUnitOfUniverses R s) ≫ l.hom =
        unit.hom ≫ ringedSectionLocalizationUnitOfUniverses S t

/-- The functor on derived categories attached to the recorded exact functor.
Source: Stacks 05RR (blueprint: lem-weil-pbc-ringed-presentation-transport). -/
abbrev RingedPresentationFunctor.derived
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    {F : PresentationModules R ⥤ PresentationModules S} (T : RingedPresentationFunctor R S F) :=
  presentationDerivedMap F T.additive T.finiteLimits T.finiteColimits

/-- The commutative restricted ring on the existing element site: `(U,s) ↦ R(U)`.
This retains exactly the underlying ring of `elementRing`, with no new site construction.
Source: Stacks 0791 and 04IE (blueprint: lem-weil-pbc-ringed-presentation-transport). -/
def presentationElementRing {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (A : Sheaf J (Type u)) :
    Sheaf (elementTopology A) CommRingCat.{u} :=
  ⟨(elementProjection A).op ⋙ R.obj,
    (elementProjection A).op_comp_isSheaf_of_isSheaf _ _ _ R.property⟩

/-- Every map of element sites induced by a sheaf arrow is continuous.
Source: Stacks 04J4; continuity is the last assertion of element-site descent.
(blueprint: def-weil-pbc-ringed-presentation-comparison-data). -/
theorem presentationElementRestriction_continuous
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {A B : Sheaf J (Type u)} (b : B ⟶ A) :
    Functor.IsContinuous (elementMap b) (elementTopology B) (elementTopology A) :=
  (element_site_descent A).2.2.2 B b

private theorem elementRestrictionRelocalization
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J RingCat.{u}) {A B : Sheaf J (Type u)} (b : B ⟶ A)
    (h : Functor.IsContinuous (elementMap b) (elementTopology B) (elementTopology A)) :
    Nonempty (elementModulePullback.{u, u} O A ⋙
      elementModulePullbackOver.{u, u} O b h ≅ elementModulePullback.{u, u} O B) := by
  refine ⟨NatIso.ofComponents (fun M ↦ Iso.refl _) ?_⟩
  intro M N f
  ext U x
  rfl

/-- Successive element restriction evaluates a module at the same underlying site object.
Source: Stacks 04J4; both composites are sectionwise restriction, so the comparison is
identity on every section and commutes with every module restriction map.
(blueprint: def-weil-pbc-ringed-presentation-comparison-data). -/
theorem presentationElementRestriction_relocalization
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) {A B : Sheaf J (Type u)} (b : B ⟶ A)
    (h : Functor.IsContinuous (elementMap b) (elementTopology B) (elementTopology A)) :
    Nonempty (elementModulePullback.{u, u} (localCoefficientRings R) A ⋙
      elementModulePullbackOver.{u, u} (localCoefficientRings R) b h ≅
        elementModulePullback.{u, u} (localCoefficientRings R) B) :=
  elementRestrictionRelocalization (localCoefficientRings R) b h

/-- A module equivalence with the comparisons which are not formal consequences
of exact equivalence. Source: Stacks 03CR and 08J7.
(blueprint: def-weil-pbc-ringed-presentation-comparison-data). -/
structure RingedPresentationEquivalenceCore
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (R : Sheaf J CommRingCat.{u}) (S : Sheaf K CommRingCat.{u}) where
  modules : PresentationModules R ≌ PresentationModules S
  forwardUnit : modules.functor.obj (SheafOfModules.unit (localCoefficientRings R)) ≅
    SheafOfModules.unit (localCoefficientRings S)
  forwardHom :
    let D := presentationDerivedMap (R := R) (S := S) modules.functor
      (Functor.additive_of_preserves_binary_products _) (inferInstance) (inferInstance)
    Nonempty (presentationRHom R ⋙ D ≅ (D.op.prod D) ⋙ presentationRHom S)

end CategoryTheory
