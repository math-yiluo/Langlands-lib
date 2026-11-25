/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.CategoryTheory.DerivedCategory.Picard.DerivedTensorSecondFactorFunctor
public import WeilConjectures.CategoryTheory.DerivedCategory.Picard.MixedTensorPointwiseLeftDerived
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import Mathlib.CategoryTheory.Abelian.ShortExact
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.LinearAlgebra.TensorProduct.Quotient

import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
/-!
# Resolution independence of exact-sections derived reduction

Source: Stacks Project, sites-cohomology.tex, Tag 06YY, and more-algebra.tex, Tag 06Y6.
(blueprint: lem-pod-derived-reduction-sheaf-resolution-independence).

The ordinary tensor models below are the quotient complexes: a specified surjective R→A
with kernel tR represents the principal quotient. Scalar extension represents C/tC,
and sheaf change of rings represents P/tP. Their comparisons are fixed
on pure tensors by the module-sheafification unit. No comparison is assumed invertible.
Site object, site morphism, coefficient and derived morphism universes remain separate.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 128

universe u v r wO wS wR wA

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open CategoryTheory.Functor
open scoped ChangeOfRings

namespace SheafOfModules
namespace PrincipalReduction

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r} ⋙
    forget₂ RingCat.{r} AddCommGrpCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasSheafify J AddCommGrpCat.{r}]

/-- Underlying additive sheaf. Source: Stacks 03DA
(blueprint: lem-pod-derived-reduction-sheaf-resolution-independence). -/
noncomputable abbrev additiveSheaf (O : Sheaf J CommRingCat.{r}) :=
  (sheafCompose J ((forget₂ CommRingCat.{r} RingCat.{r} ⋙
    forget₂ RingCat.{r} AddCommGrpCat.{r}))).obj O

/-- Multiplication by a final-object section is uniquely specified on every section.
Source: Stacks 03CV (blueprint: lem-pod-derived-reduction-sheaf-resolution-independence).
Proof: at V multiply by the restriction of a. Restrictions preserve products, so these
additive maps form a sheaf morphism. Equality of all components gives uniqueness. -/
theorem existsUnique_sectionMultiplication (O : Sheaf J CommRingCat.{r})
    (U : C) (hU : IsTerminal U) (a : O.obj.obj (op U)) :
    ∃! μ : additiveSheaf O ⟶ additiveSheaf O,
      ∀ (V : C) (x : O.obj.obj (op V)),
        μ.hom.app (op V) x = O.obj.map (hU.from V).op a * x := by
  let μ : additiveSheaf O ⟶ additiveSheaf O :=
    ⟨{ app := fun V ↦ AddCommGrpCat.ofHom
          (show O.obj.obj V →+ O.obj.obj V from
          { toFun := fun x ↦ O.obj.map (hU.from V.unop).op a * x
            map_zero' := mul_zero _
            map_add' := mul_add _ })
       naturality := by
          intro V W f
          ext x
          change O.obj.obj V at x
          symm
          change O.obj.map f (_ * x) = _ * O.obj.map f x
          rw [map_mul]
          congr 1
          rw [← ConcreteCategory.comp_apply, ← O.obj.map_comp]
          have hh : (hU.from V.unop).op ≫ f = (hU.from W.unop).op := by
            apply Quiver.Hom.unop_inj
            exact hU.hom_ext _ _
          rw [hh] }⟩
  refine ⟨μ, fun V x ↦ rfl, ?_⟩
  intro ν hν
  ext V x
  exact hν V.unop x

/-- Multiplication by the specified section, determined uniquely sectionwise.
Source: Stacks 03CV (blueprint: lem-pod-derived-reduction-sheaf-resolution-independence). -/
noncomputable def sectionMultiplication (O : Sheaf J CommRingCat.{r})
    (U : C) (hU : IsTerminal U) (a : O.obj.obj (op U)) :
    additiveSheaf O ⟶ additiveSheaf O :=
  (existsUnique_sectionMultiplication O U hU a).exists.choose

/-- The hypotheses of the exact-sections principal quotient comparison. The short exact
sequence is in abelian sheaves, so its epimorphism is not required to be sectionwise
surjective. Source: Stacks 06YY and the extracted exact-sections coherence argument
(blueprint: lem-pod-derived-reduction-sheaf-resolution-independence). -/
structure Setup (R : Type r) [CommRing R] where
  /-- The final object at which sections are taken. -/
  U : C
  /-- Finality. -/
  terminal : IsTerminal U
  /-- The original coefficient sheaf. -/
  O : Sheaf J CommRingCat.{r}
  /-- Its principal quotient sheaf. -/
  S : Sheaf J CommRingCat.{r}
  /-- The original coefficient map. -/
  ρ : R →+* O.obj.obj (op U)
  /-- The element defining the quotient. -/
  t : R
  /-- The sheaf quotient map. -/
  φ : O ⟶ S
  /-- A specified presentation of the quotient coefficient ring. -/
  A : Type r
  /-- Its commutative ring structure. -/
  [commRing : CommRing A]
  /-- The specified quotient homomorphism. -/
  quotientMap : R →+* A
  /-- The quotient homomorphism is onto. -/
  quotient_surjective : Function.Surjective quotientMap
  /-- Its kernel is generated by t, with a normalized elementwise formula. -/
  quotient_kernel : ∀ x : R, quotientMap x = 0 ↔ ∃ y : R, t * y = x
  /-- The actual quotient-section coefficient map. -/
  quotientSectionsMap : A →+* S.obj.obj (op U)
  /-- Both scalar maps come from the same coefficient projection. -/
  quotient_sections_comm : ∀ x : R,
    quotientSectionsMap (quotientMap x) = (φ.hom.app (op U)) (ρ x)
  /-- The coefficient sequence is a complex. -/
  zero : sectionMultiplication O U terminal (ρ t) ≫
    (sheafCompose J ((forget₂ CommRingCat.{r} RingCat.{r} ⋙
    forget₂ RingCat.{r} AddCommGrpCat.{r}))).map φ = 0
  /-- Exactness including injectivity and epimorphy. -/
  shortExact : (ShortComplex.mk (sectionMultiplication O U terminal (ρ t))
    ((sheafCompose J ((forget₂ CommRingCat.{r} RingCat.{r} ⋙
    forget₂ RingCat.{r} AddCommGrpCat.{r}))).map φ) zero).ShortExact
  /-- Exactness of abelian sections, with no boundedness hypothesis. -/
  sectionsExact : exactFunctor _ _ ((sheafSections J AddCommGrpCat.{r}).obj (op U))

attribute [instance] Setup.commRing

namespace Setup

variable {R : Type r} [CommRing R] (D : Setup (C := C) (J := J) R)

/-- Integral sections with restriction along rho. Source: Stacks 03CW
(blueprint: lem-pod-derived-reduction-sheaf-resolution-independence). -/
noncomputable abbrev sections :
    ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.O) ⥤
      ModuleCat.{r} R :=
  evaluation (derivedChangeRingIndependentCoefficients J D.O) (op D.U) ⋙
    ModuleCat.restrictScalars D.ρ

/-- Quotient sections with their actual R/(t) action. Source: Stacks 03CW
(blueprint: lem-pod-derived-reduction-sheaf-resolution-independence). -/
noncomputable abbrev quotientSections :
    ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.S) ⥤
      ModuleCat.{r} D.A :=
  evaluation (derivedChangeRingIndependentCoefficients J D.S) (op D.U) ⋙
    ModuleCat.restrictScalars D.quotientSectionsMap

/-- Exact abelian sections induce exact module sections, for either coefficient map.
Source: Stacks 03DA, 05RU
(blueprint: lem-pod-derived-reduction-sheaf-resolution-independence).
Proof: kernels, images and cokernels of module sheaves have the same underlying
abelian sheaves. Apply D.sectionsExact and note that restriction of scalars changes
none of these groups. The argument applies to both coefficient rings. -/
theorem sections_exact :
    (PreservesFiniteLimits D.sections ∧ PreservesFiniteColimits D.sections) ∧
    (PreservesFiniteLimits D.quotientSections ∧
      PreservesFiniteColimits D.quotientSections) := by
  have h := (exactFunctor_iff _).mp D.sectionsExact
  have : PreservesFiniteLimits ((sheafSections J AddCommGrpCat.{r}).obj (op D.U)) := h.1
  have : PreservesFiniteColimits ((sheafSections J AddCommGrpCat.{r}).obj (op D.U)) := h.2
  have evalExact (O : Sheaf J RingCat.{r}) (B : Type r) [CommRing B]
      (f : B →+* O.obj.obj (op D.U)) :
      PreservesFiniteLimits (evaluation O (op D.U) ⋙ ModuleCat.restrictScalars f) ∧
      PreservesFiniteColimits (evaluation O (op D.U) ⋙ ModuleCat.restrictScalars f) := by
    have : PreservesFiniteColimits (toSheaf.{r} O) := inferInstance
    let F := evaluation O (op D.U) ⋙ ModuleCat.restrictScalars f
    have : PreservesFiniteColimits (F ⋙ forget₂ (ModuleCat.{r} B) AddCommGrpCat.{r}) :=
      inferInstanceAs (PreservesFiniteColimits
        (toSheaf O ⋙ (sheafSections J AddCommGrpCat.{r}).obj (op D.U)))
    have : PreservesFiniteLimits (F ⋙ forget₂ (ModuleCat.{r} B) AddCommGrpCat.{r}) :=
      inferInstanceAs (PreservesFiniteLimits
        (toSheaf O ⋙ (sheafSections J AddCommGrpCat.{r}).obj (op D.U)))
    exact ⟨preservesFiniteLimits_of_reflects_of_preserves F (forget₂ _ AddCommGrpCat.{r}),
      preservesFiniteColimits_of_reflects_of_preserves F (forget₂ _ AddCommGrpCat.{r})⟩
  exact ⟨evalExact (derivedChangeRingIndependentCoefficients J D.O) R D.ρ,
    evalExact (derivedChangeRingIndependentCoefficients J D.S) D.A D.quotientSectionsMap⟩

/-- Exact integral sections preserve finite limits. Source: Stacks 03DA
(blueprint: lem-pod-derived-reduction-sheaf-resolution-independence). -/
noncomputable instance sectionsLimits : PreservesFiniteLimits D.sections :=
  (sections_exact D).1.1

/-- Exact integral sections preserve finite colimits. Source: Stacks 03DA
(blueprint: lem-pod-derived-reduction-sheaf-resolution-independence). -/
noncomputable instance sectionsColimits : PreservesFiniteColimits D.sections :=
  (sections_exact D).1.2

/-- Exact quotient sections preserve finite limits. Source: Stacks 03DA
(blueprint: lem-pod-derived-reduction-sheaf-resolution-independence). -/
noncomputable instance quotientSectionsLimits : PreservesFiniteLimits D.quotientSections :=
  (sections_exact D).2.1

/-- Exact quotient sections preserve finite colimits. Source: Stacks 03DA
(blueprint: lem-pod-derived-reduction-sheaf-resolution-independence). -/
noncomputable instance quotientSectionsColimits : PreservesFiniteColimits D.quotientSections :=
  (sections_exact D).2.2

/-- Additivity of exact integral sections, inherited from preservation of products.
Source: Stacks 03DA (blueprint: lem-pod-derived-reduction-sheaf-resolution-independence). -/
noncomputable instance sectionsAdditive : D.sections.Additive :=
  Functor.additive_of_preserves_binary_products D.sections

/-- Additivity of exact quotient sections, inherited from preservation of products.
Source: Stacks 03DA (blueprint: lem-pod-derived-reduction-sheaf-resolution-independence). -/
noncomputable instance quotientSectionsAdditive : D.quotientSections.Additive :=
  Functor.additive_of_preserves_binary_products D.quotientSections

private noncomputable abbrev Omod : Sheaf J RingCat.{r} :=
  ⟨D.O.obj ⋙ forget₂ CommRingCat.{r} RingCat.{r},
    GrothendieckTopology.HasSheafCompose.isSheaf _ D.O.property⟩

private noncomputable abbrev Smod : Sheaf J RingCat.{r} :=
  ⟨D.S.obj ⋙ forget₂ CommRingCat.{r} RingCat.{r},
    GrothendieckTopology.HasSheafCompose.isSheaf _ D.S.property⟩

private noncomputable abbrev coefficientRestriction :=
  (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map D.φ

private noncomputable def coefficientMultiplication : unit D.Omod ⟶ unit D.Omod where
  val :=
    { app := fun V ↦ by
        change ModuleCat.of (D.O.obj.obj V) (D.O.obj.obj V) ⟶
          ModuleCat.of (D.O.obj.obj V) (D.O.obj.obj V)
        exact ModuleCat.ofHom
          { toFun := fun x ↦ D.O.obj.map (D.terminal.from V.unop).op (D.ρ D.t) * x
            map_add' := mul_add _
            map_smul' := fun b x ↦ mul_left_comm _ _ _ }
      naturality := by
        intro V W f
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        change D.O.obj.obj V at x
        symm
        change D.O.obj.map f (_ * x) = _ * D.O.obj.map f x
        rw [map_mul]
        congr 1
        rw [← ConcreteCategory.comp_apply, ← D.O.obj.map_comp]
        have hh : (D.terminal.from V.unop).op ≫ f =
            (D.terminal.from W.unop).op := by
          apply Quiver.Hom.unop_inj
          exact D.terminal.hom_ext _ _
        rw [hh] }

private noncomputable def coefficientProjection :
    unit D.Omod ⟶ (restrictScalars D.coefficientRestriction).obj (unit D.Smod) where
  val :=
    { app := fun V ↦ by
        change ModuleCat.of (D.O.obj.obj V) (D.O.obj.obj V) ⟶
          (ModuleCat.restrictScalars (D.φ.hom.app V).hom).obj
            (ModuleCat.of (D.S.obj.obj V) (D.S.obj.obj V))
        exact ModuleCat.ofHom
          (Y := (ModuleCat.restrictScalars (D.φ.hom.app V).hom).obj
            (ModuleCat.of (D.S.obj.obj V) (D.S.obj.obj V)))
          { toFun := D.φ.hom.app V
            map_add' := map_add _
            map_smul' := fun b x ↦ by
              change D.φ.hom.app V (b * x) = D.φ.hom.app V b * D.φ.hom.app V x
              exact map_mul _ _ _ }
      naturality := by
        intro V W f
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        exact ConcreteCategory.congr_hom (D.φ.hom.naturality f) x }

private theorem coefficientMultiplication_underlying :
    (toSheaf D.Omod).map D.coefficientMultiplication =
      sectionMultiplication D.O D.U D.terminal (D.ρ D.t) := by
  apply (existsUnique_sectionMultiplication D.O D.U D.terminal (D.ρ D.t)).unique
  · intro V x
    rfl
  · exact (existsUnique_sectionMultiplication D.O D.U D.terminal (D.ρ D.t)).exists.choose_spec

private theorem coefficient_zero :
    D.coefficientMultiplication ≫ D.coefficientProjection = 0 := by
  apply (toSheaf D.Omod).map_injective
  rw [Functor.map_comp, coefficientMultiplication_underlying]
  ext V x
  exact congrArg (fun f ↦ f.hom.app V x) D.zero

private theorem coefficient_shortExact :
    (ShortComplex.mk D.coefficientMultiplication D.coefficientProjection
      D.coefficient_zero).ShortExact := by
  apply ShortExact.reflects_shortExact_of_faithful (toSheaf D.Omod)
  have e : (ShortComplex.mk D.coefficientMultiplication D.coefficientProjection
      D.coefficient_zero).map (toSheaf D.Omod) ≅
      ShortComplex.mk (sectionMultiplication D.O D.U D.terminal (D.ρ D.t))
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r} ⋙
          forget₂ RingCat.{r} AddCommGrpCat.{r})).map D.φ) D.zero :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by
        change 𝟙 _ ≫ sectionMultiplication D.O D.U D.terminal (D.ρ D.t) =
          (toSheaf D.Omod).map D.coefficientMultiplication ≫ 𝟙 _
        simp only [Category.id_comp, Category.comp_id]
        exact (coefficientMultiplication_underlying D).symm)
      (by ext V x; rfl)
  exact (ShortComplex.shortExact_iff_of_iso e).2 D.shortExact

private noncomputable def tensorUnitIso
    (M : ringedSiteModules.{r} D.Omod) :
    (siteSheafTensorRight (A := D.O) M).obj (unit D.Omod) ≅ M :=
  (PresheafOfModules.sheafification (𝟙 D.Omod.obj)).mapIso
      ((siteTensorRightIso D.O M.val).app (unit D.Omod).val ≪≫ λ_ M.val) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 D.Omod.obj)).counit).app M

private noncomputable def restrictedSheafification
    (P : PresheafOfModules.{r} D.Smod.obj) :
    (PresheafOfModules.sheafification.{r} (𝟙 D.Omod.obj)).obj
      ((PresheafOfModules.restrictScalars.{r} D.coefficientRestriction.hom).obj P) ⟶
      (restrictScalars.{r} D.coefficientRestriction).obj
        ((PresheafOfModules.sheafification.{r} (𝟙 D.Smod.obj)).obj P) := by
  refine (PresheafOfModules.sheafificationHomEquiv.{r}
    (P := (PresheafOfModules.restrictScalars.{r} D.coefficientRestriction.hom).obj P)
    (F := (restrictScalars.{r} D.coefficientRestriction).obj
      ((PresheafOfModules.sheafification.{r} (𝟙 D.Smod.obj)).obj P))
    (𝟙 D.Omod.obj)).symm ?_
  exact (PresheafOfModules.restrictScalars.{r} D.coefficientRestriction.hom).map
    ((PresheafOfModules.sheafificationAdjunction (𝟙 D.Smod.obj)).unit.app P)

attribute [local irreducible] restrictedSheafification

set_option backward.isDefEq.respectTransparency false in
private theorem restrictedSheafification_underlying
    (P : PresheafOfModules.{r} D.Smod.obj) :
    IsIso ((toSheaf D.Omod).map (D.restrictedSheafification P)) := by
  rw [restrictedSheafification,
    PresheafOfModules.toSheaf_map_sheafificationHomEquiv_symm]
  have h : (PresheafOfModules.toPresheaf D.Omod.obj).map
      ((PresheafOfModules.restrictScalars D.coefficientRestriction.hom).map
        ((PresheafOfModules.sheafificationAdjunction (𝟙 D.Smod.obj)).unit.app P)) =
      CategoryTheory.toSheafify J P.presheaf := by
    exact PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app
      (𝟙 D.Smod.obj) P
  let adj := CategoryTheory.sheafificationAdjunction J AddCommGrpCat.{r}
  change IsIso ((adj.homEquiv P.presheaf
    ((presheafToSheaf J AddCommGrpCat.{r}).obj P.presheaf)).symm
      (adj.unit.app P.presheaf))
  have hh := adj.homEquiv_symm_unit P.presheaf
  exact hh.symm ▸ IsIso.id _

private theorem restrictedSheafification_isIso
    (P : PresheafOfModules.{r} D.Smod.obj) :
    IsIso (D.restrictedSheafification P) := by
  have : IsIso ((toSheaf D.Omod).map (D.restrictedSheafification P)) :=
    D.restrictedSheafification_underlying P
  exact isIso_of_reflects_iso _ (toSheaf D.Omod)

private noncomputable def tensorQuotientPresheafIso
    (M : ringedSiteModules.{r} D.Omod) :
    siteTensorPresheaf (R := D.O.obj)
        ((restrictScalars D.coefficientRestriction).obj (unit D.Smod)).val M.val ≅
      (PresheafOfModules.restrictScalars D.coefficientRestriction.hom).obj
        (changeOfRingsPresheaf D.φ M) := by
  refine PresheafOfModules.isoMk (fun V ↦ ?_) ?_
  · exact (LinearEquiv.refl (D.O.obj.obj V)
      (TensorProduct (D.O.obj.obj V)
        ((ModuleCat.restrictScalars (D.φ.hom.app V).hom).obj
          (ModuleCat.of (D.S.obj.obj V) (D.S.obj.obj V))) (M.val.obj V))).toModuleIso
  · intro V W f
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro b x
    exact (Classical.choose_spec (exists_changeOfRingsMap D.φ M f) b x).symm

private noncomputable def tensorQuotientIso
    (M : ringedSiteModules.{r} D.Omod) :
    (siteSheafTensorRight (A := D.O) M).obj
        ((restrictScalars D.coefficientRestriction).obj (unit D.Smod)) ≅
      (restrictScalars D.coefficientRestriction).obj (changeOfRings D.φ M) := by
  letI := D.restrictedSheafification_isIso (changeOfRingsPresheaf D.φ M)
  exact (PresheafOfModules.sheafification (𝟙 D.Omod.obj)).mapIso
      (D.tensorQuotientPresheafIso M) ≪≫
    asIso (D.restrictedSheafification (changeOfRingsPresheaf D.φ M))

attribute [local irreducible] tensorUnitIso tensorQuotientPresheafIso tensorQuotientIso

private theorem quotientTensor_bijective
    (M : ModuleCat.{r} R) (N : ModuleCat.{r} D.A)
    (f : (ModuleCat.extendScalars D.quotientMap).obj M ⟶ N)
    (hs : Function.Surjective (fun x : M ↦ f ((1 : D.A) ⊗ₜ[R, D.quotientMap] x)))
    (hk : ∀ x : M, f ((1 : D.A) ⊗ₜ[R, D.quotientMap] x) = 0 →
      ∃ y : M, D.t • y = x) : Function.Bijective f := by
  let := D.quotientMap.toAlgebra
  have hu : Function.Surjective
      (fun x : M ↦ (1 : D.A) ⊗ₜ[R, D.quotientMap] x) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | add z w hz hw =>
      obtain ⟨x, rfl⟩ := hz
      obtain ⟨y, rfl⟩ := hw
      exact ⟨x + y, TensorProduct.tmul_add _ _ _⟩
    | tmul a x =>
      obtain ⟨b, rfl⟩ := D.quotient_surjective a
      refine ⟨b • x, ?_⟩
      change (1 : D.A) ⊗ₜ[R] (b • x) = D.quotientMap b ⊗ₜ[R] x
      rw [TensorProduct.tmul_smul]
      change (D.quotientMap b * 1) ⊗ₜ[R] x = _
      rw [mul_one]
  constructor
  · apply (injective_iff_map_eq_zero f.hom).2
    intro z hz
    obtain ⟨x, rfl⟩ := hu z
    obtain ⟨y, rfl⟩ := hk x hz
    change (1 : D.A) ⊗ₜ[R] (D.t • y) = 0
    rw [TensorProduct.tmul_smul]
    change (D.quotientMap D.t * 1) ⊗ₜ[R] y = 0
    rw [(D.quotient_kernel D.t).2 ⟨1, mul_one _⟩, zero_mul, TensorProduct.zero_tmul]
  · intro n
    obtain ⟨x, hx⟩ := hs n
    exact ⟨_, hx⟩

set_option backward.isDefEq.respectTransparency false in
private theorem tensorUnitIso_unit
    (M : ringedSiteModules.{r} D.Omod) (V : Cᵒᵖ) (x : M.val.obj V) :
    (D.tensorUnitIso M).hom.val.app V
      (((PresheafOfModules.sheafificationAdjunction (𝟙 D.Omod.obj)).unit.app
        (siteTensorPresheaf (unit D.Omod).val M.val)).app V
          ((1 : D.O.obj.obj V) ⊗ₜ[D.O.obj.obj V] x)) = x := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 D.Omod.obj)
  let f := ((siteTensorRightIso D.O M.val).app (unit D.Omod).val ≪≫ λ_ M.val).hom
  have hn := adj.unit.naturality f
  have ht := adj.right_triangle_components M
  have hn' := congrArg (fun g ↦ g.app V
    ((1 : D.O.obj.obj V) ⊗ₜ[D.O.obj.obj V] x)) hn
  have ht' := congrArg (fun g ↦ g.app V x) ht
  simp only [PresheafOfModules.comp_app, ModuleCat.comp_apply] at hn' ht'
  change (D.tensorUnitIso M).hom.val.app V _ = _
  simp only [tensorUnitIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom, asIso_hom, comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  erw [← hn']
  have hf : f.app V ((1 : D.O.obj.obj V) ⊗ₜ[D.O.obj.obj V] x) = x := by
    change (1 : D.O.obj.obj V) • x = x
    exact one_smul _ _
  change (adj.counit.app M).val.app V ((adj.unit.app M.val).app V
    (f.app V ((1 : D.O.obj.obj V) ⊗ₜ[D.O.obj.obj V] x))) = x
  rw [hf]
  exact ht'

private theorem tensorUnitIso_inv_apply
    (M : ringedSiteModules.{r} D.Omod) (V : Cᵒᵖ) (x : M.val.obj V) :
    (D.tensorUnitIso M).inv.val.app V x =
      ((PresheafOfModules.sheafificationAdjunction (𝟙 D.Omod.obj)).unit.app
        (siteTensorPresheaf (unit D.Omod).val M.val)).app V
          ((1 : D.O.obj.obj V) ⊗ₜ[D.O.obj.obj V] x) := by
  apply_fun (D.tensorUnitIso M).hom.val.app V
  · have h := congrArg (fun g ↦ g.val.app V x) (D.tensorUnitIso M).inv_hom_id
    exact h.trans (D.tensorUnitIso_unit M V x).symm
  · intro a b hab
    have h := congrArg ((D.tensorUnitIso M).inv.val.app V) hab
    have hc := congrArg (fun g ↦ g.val.app V) (D.tensorUnitIso M).hom_inv_id
    have ha := ConcreteCategory.congr_hom hc a
    have hb := ConcreteCategory.congr_hom hc b
    exact ha.symm.trans (h.trans hb)

private theorem restrictedSheafification_unit
    (P : PresheafOfModules.{r} D.Smod.obj) (V : Cᵒᵖ) (x : P.obj V) :
    (D.restrictedSheafification P).val.app V
      (((PresheafOfModules.sheafificationAdjunction (𝟙 D.Omod.obj)).unit.app
        ((PresheafOfModules.restrictScalars D.coefficientRestriction.hom).obj P)).app V x) =
      ((PresheafOfModules.sheafificationAdjunction (𝟙 D.Smod.obj)).unit.app P).app V x := by
  unfold restrictedSheafification
  have h := (PresheafOfModules.sheafificationHomEquiv
    (P := (PresheafOfModules.restrictScalars D.coefficientRestriction.hom).obj P)
    (F := (restrictScalars D.coefficientRestriction).obj
      ((PresheafOfModules.sheafification (𝟙 D.Smod.obj)).obj P))
    (𝟙 D.Omod.obj)).apply_symm_apply
    ((PresheafOfModules.restrictScalars D.coefficientRestriction.hom).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 D.Smod.obj)).unit.app P))
  have hh := congrArg (fun g ↦ g.app V x) h
  exact hh

private noncomputable def quotientMorphism
    (M : ringedSiteModules.{r} D.Omod) :
    M ⟶ (restrictScalars D.coefficientRestriction).obj (changeOfRings D.φ M) :=
  (D.tensorUnitIso M).inv ≫ (siteSheafTensorRight (A := D.O) M).map
    D.coefficientProjection ≫ (D.tensorQuotientIso M).hom

set_option backward.isDefEq.respectTransparency false in
private theorem quotientMorphism_apply
    (M : ringedSiteModules.{r} D.Omod) (V : Cᵒᵖ) (x : M.val.obj V) :
    (D.quotientMorphism M).val.app V x =
      ((PresheafOfModules.sheafificationAdjunction (𝟙 D.Smod.obj)).unit.app
        (changeOfRingsPresheaf D.φ M)).app V
          ((1 : D.S.obj.obj V) ⊗ₜ[D.O.obj.obj V, (D.φ.hom.app V).hom] x) := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 D.Omod.obj)
  let g := siteTensorHom D.coefficientProjection.val M.val
  let k := (D.tensorQuotientPresheafIso M).hom
  have hg := congrArg (fun f ↦ f.app V
    ((1 : D.O.obj.obj V) ⊗ₜ[D.O.obj.obj V] x)) (adj.unit.naturality g)
  have hk := congrArg (fun f ↦ f.app V
    ((show ((restrictScalars D.coefficientRestriction).obj (unit D.Smod)).val.obj V
      from (1 : D.S.obj.obj V)) ⊗ₜ[D.O.obj.obj V] x))
      (adj.unit.naturality k)
  simp only [PresheafOfModules.comp_app, ModuleCat.comp_apply] at hg hk
  have hg1 : g.app V ((1 : D.O.obj.obj V) ⊗ₜ[D.O.obj.obj V] x) =
      ((show ((restrictScalars D.coefficientRestriction).obj (unit D.Smod)).val.obj V
        from (1 : D.S.obj.obj V)) ⊗ₜ[D.O.obj.obj V] x) := by
    change (D.φ.hom.app V (1 : D.O.obj.obj V)) ⊗ₜ[D.O.obj.obj V,
      (D.φ.hom.app V).hom] x = _
    rw [map_one]
  change ((adj.unit.app _).app V) (g.app V _) = _ at hg
  rw [hg1] at hg
  simp only [quotientMorphism, comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  erw [tensorUnitIso_inv_apply]
  change (D.tensorQuotientIso M).hom.val.app V
    ((PresheafOfModules.sheafification (𝟙 D.Omod.obj)).map g |>.val.app V <| _) = _
  erw [← hg]
  simp only [tensorQuotientIso, Iso.trans_hom, Functor.mapIso_hom, asIso_hom,
    comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  change (D.restrictedSheafification (changeOfRingsPresheaf D.φ M)).val.app V
    (((PresheafOfModules.sheafification (𝟙 D.Omod.obj)).map k).val.app V
      ((adj.unit.app (siteTensorPresheaf
        ((restrictScalars D.coefficientRestriction).obj (unit D.Smod)).val M.val)).app V
        ((show ((restrictScalars D.coefficientRestriction).obj (unit D.Smod)).val.obj V
          from (1 : D.S.obj.obj V)) ⊗ₜ[D.O.obj.obj V] x))) = _
  erw [← hk]
  have hk1 : k.app V
      ((show ((restrictScalars D.coefficientRestriction).obj (unit D.Smod)).val.obj V
        from (1 : D.S.obj.obj V)) ⊗ₜ[D.O.obj.obj V] x) =
      (1 : D.S.obj.obj V) ⊗ₜ[D.O.obj.obj V, (D.φ.hom.app V).hom] x := by
    dsimp only [k]
    unfold tensorQuotientPresheafIso
    rfl
  change (D.restrictedSheafification (changeOfRingsPresheaf D.φ M)).val.app V
    ((adj.unit.app _).app V (k.app V _)) = _
  rw [hk1]
  exact D.restrictedSheafification_unit _ V _

private noncomputable def tensorMultiplication
    (M : ringedSiteModules.{r} D.Omod) : M ⟶ M :=
  (D.tensorUnitIso M).inv ≫ (siteSheafTensorRight (A := D.O) M).map
    D.coefficientMultiplication ≫ (D.tensorUnitIso M).hom

set_option backward.isDefEq.respectTransparency false in
private theorem tensorMultiplication_apply
    (M : ringedSiteModules.{r} D.Omod) (V : Cᵒᵖ) (x : M.val.obj V) :
    (D.tensorMultiplication M).val.app V x =
      D.O.obj.map (D.terminal.from V.unop).op (D.ρ D.t) • x := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 D.Omod.obj)
  let g := siteTensorHom D.coefficientMultiplication.val M.val
  have hg := congrArg (fun f ↦ f.app V
    ((1 : D.O.obj.obj V) ⊗ₜ[D.O.obj.obj V] x)) (adj.unit.naturality g)
  simp only [PresheafOfModules.comp_app, ModuleCat.comp_apply] at hg
  simp only [tensorMultiplication, comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply]
  erw [tensorUnitIso_inv_apply]
  change (D.tensorUnitIso M).hom.val.app V
    ((PresheafOfModules.sheafification (𝟙 D.Omod.obj)).map g |>.val.app V <| _) = _
  erw [← hg]
  change (D.tensorUnitIso M).hom.val.app V
    ((adj.unit.app (siteTensorPresheaf (unit D.Omod).val M.val)).app V
      ((D.O.obj.map (D.terminal.from V.unop).op (D.ρ D.t) * 1) ⊗ₜ[D.O.obj.obj V] x)) = _
  rw [mul_one]
  have ht : (D.O.obj.map (D.terminal.from V.unop).op (D.ρ D.t)) ⊗ₜ[D.O.obj.obj V] x =
      (1 : D.O.obj.obj V) ⊗ₜ[D.O.obj.obj V]
        (D.O.obj.map (D.terminal.from V.unop).op (D.ρ D.t) • x) := by
    have hh := TensorProduct.smul_tmul (R := D.O.obj.obj V) (R' := D.O.obj.obj V)
      (D.O.obj.map (D.terminal.from V.unop).op (D.ρ D.t))
      (1 : D.O.obj.obj V) x
    simpa only [smul_eq_mul, mul_one] using hh
  rw [ht]
  exact D.tensorUnitIso_unit M V _

private theorem tensorMultiplication_quotientMorphism
    (M : ringedSiteModules.{r} D.Omod) :
    D.tensorMultiplication M ≫ D.quotientMorphism M = 0 := by
  simp only [tensorMultiplication, quotientMorphism, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc ((siteSheafTensorRight (A := D.O) M).map _),
    ← Functor.map_comp, coefficient_zero, Functor.map_zero, Limits.zero_comp,
    Limits.comp_zero]

private noncomputable def tensorShortComplex
    (M : ringedSiteModules.{r} D.Omod) : ShortComplex (ringedSiteModules.{r} D.Omod) :=
  ShortComplex.mk (D.tensorMultiplication M) (D.quotientMorphism M)
    (D.tensorMultiplication_quotientMorphism M)

private theorem tensorShortComplex_shortExact
    (M : ringedSiteModules.{r} D.Omod) (hf : IsFlatOnSite (R := D.O) M) :
    (D.tensorShortComplex M).ShortExact := by
  have he := (exactFunctor_iff _).1 hf
  let := he.1
  let := he.2
  let F := siteSheafTensorRight (A := D.O) M
  have hs := (D.coefficient_shortExact).map_of_exact F
  let e : (ShortComplex.mk D.coefficientMultiplication D.coefficientProjection
      D.coefficient_zero).map F ≅ D.tensorShortComplex M :=
    ShortComplex.isoMk (D.tensorUnitIso M) (D.tensorUnitIso M) (D.tensorQuotientIso M)
      (by
        dsimp only [tensorShortComplex, F, ShortComplex.map]
        unfold tensorMultiplication
        simp only [Iso.hom_inv_id_assoc])
      (by
        dsimp only [tensorShortComplex, F, ShortComplex.map]
        unfold quotientMorphism
        simp only [Iso.hom_inv_id_assoc])
  exact (ShortComplex.shortExact_iff_of_iso e).1 hs

set_option backward.isDefEq.respectTransparency true

variable [HasDerivedCategory.{wO}
    (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.O))]
  [HasDerivedCategory.{wS}
    (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.S))]
  [HasDerivedCategory.{wR} (ModuleCat.{r} R)]
  [HasDerivedCategory.{wA} (ModuleCat.{r} D.A)]

/-- G, obtained from exact sections by localization. Source: Stacks 05RU
(blueprint: lem-pod-derived-reduction-sheaf-resolution-independence). -/
noncomputable abbrev G := D.sections.mapDerivedCategory

/-- G', obtained from exact quotient sections by localization. Source: Stacks 05RU
(blueprint: lem-pod-derived-reduction-sheaf-resolution-independence). -/
noncomputable abbrev G' := D.quotientSections.mapDerivedCategory

/-- The canonical universal derived-extension pair, including its counit. Its ordinary
objects and maps are prescribed and its derived pair is determined up to the unique
counit-compatible isomorphism. Source: Stacks 06YY
(blueprint: lem-pod-derived-reduction-sheaf-resolution-independence). -/
noncomputable def extension :=
  (nonempty_derivedChangeOfRingsCochainModel.{u, v, r, wO, wS} D.φ).some

attribute [local irreducible] extension

/-- Termwise sheaf quotient P/tP, using the recorded change-of-rings functor.
Source: Stacks 03EK, 06YY
(blueprint: lem-pod-derived-reduction-sheaf-resolution-independence). -/
noncomputable abbrev quotientComplex := D.extension.E.mapHomologicalComplex (.up ℤ)

/-- Derived sheaf quotient T. Source: Stacks 06YY
(blueprint: lem-pod-derived-reduction-sheaf-resolution-independence). -/
noncomputable abbrev T := D.extension.T

/-- A[0], with the regular quotient-module action. Source: Stacks 06Y6
(blueprint: lem-pod-derived-reduction-sheaf-resolution-independence). -/
noncomputable abbrev quotientSingle :=
  (HomologicalComplex.single (ModuleCat.{r} D.A) (.up ℤ) 0).obj
    (𝟙_ (ModuleCat.{r} D.A))

/-- The second-factor derived-tensor functor supplied by its recorded dependency.
Source: Stacks 06Y6 (blueprint: lem-pod-derived-reduction-sheaf-resolution-independence). -/
noncomputable abbrev tensorFamily :=
  (DerivedCategory.exists_derivedTensor_second_factor_functor D.quotientMap).2.choose

/-- The universal family of ordinary-module tensor counits. Source: Stacks 06Y6
(blueprint: lem-pod-derived-reduction-sheaf-resolution-independence). -/
noncomputable abbrev tensorFamilyCounit :=
  (DerivedCategory.exists_derivedTensor_second_factor_functor D.quotientMap).2.choose_spec.choose

/-- L = - tensor_R^L A, without any flatness assumption on A. Source: Stacks 06Y6
(blueprint: lem-pod-derived-reduction-sheaf-resolution-independence). -/
noncomputable abbrev L := D.tensorFamily.obj D.quotientSingle

/-- The universal property for the specified second-factor functor at A[0].
Source: Stacks 06Y6 (blueprint: lem-pod-derived-reduction-sheaf-resolution-independence). -/
noncomputable instance tensorFamilyUniversal :
    D.L.IsLeftDerivedFunctor (D.tensorFamilyCounit D.quotientSingle)
      (HomologicalComplex.quasiIso (ModuleCat.{r} R) (.up ℤ)) :=
  (DerivedCategory.exists_derivedTensor_second_factor_functor
    D.quotientMap).2.choose_spec.choose_spec.1 D.quotientSingle

/-- The pointwise universal tensor pair of the recorded mixed-tensor dependency.
Source: Stacks 064L, 06Y6
(blueprint: lem-pod-derived-reduction-sheaf-resolution-independence). -/
noncomputable abbrev pointwiseTensor :=
  (DerivedCategory.exists_mixedTensor_pointwise_leftDerived
    D.quotientMap D.quotientSingle).choose

/-- Its actual natural counit, before specialization to the quotient complex.
Source: Stacks 064L, 06Y6
(blueprint: lem-pod-derived-reduction-sheaf-resolution-independence). -/
noncomputable abbrev pointwiseCounit :=
  (DerivedCategory.exists_mixedTensor_pointwise_leftDerived
    D.quotientMap D.quotientSingle).choose_spec.choose

/-- The pointwise mixed-tensor counit has the universal derived property.
Source: Stacks 064L, 06Y6
(blueprint: lem-pod-derived-reduction-sheaf-resolution-independence). -/
noncomputable instance pointwiseUniversal :
    D.pointwiseTensor.IsLeftDerivedFunctor D.pointwiseCounit
      (HomologicalComplex.quasiIso (ModuleCat.{r} R) (.up ℤ)) :=
  (DerivedCategory.exists_mixedTensor_pointwise_leftDerived
    D.quotientMap D.quotientSingle).choose_spec.choose_spec.1

/-- Tensor with A[0] is termwise scalar extension: the single-factor totalization
comparison followed by the ordinary tensor unitor. This is the quotient model C/tC.
Source: Stacks 06Y6 (blueprint: lem-pod-derived-reduction-sheaf-resolution-independence). -/
noncomputable def tensorSingleIso (K : CochainComplex (ModuleCat.{r} R) ℤ) :
    (((ModuleCat.mixedTensor D.quotientMap).flip.map₂CochainComplex).obj K).obj
      D.quotientSingle ≅
      ((ModuleCat.extendScalars D.quotientMap).mapHomologicalComplex (.up ℤ)).obj K :=
  CochainComplex.mapBifunctorSingle₂Iso (ModuleCat.mixedTensor D.quotientMap).flip
      (𝟙_ (ModuleCat.{r} D.A)) K ≪≫
    (NatIso.mapHomologicalComplex
      (isoWhiskerLeft (ModuleCat.extendScalars D.quotientMap)
        (leftUnitorNatIso (ModuleCat.{r} D.A)) ≪≫ Functor.rightUnitor _) (.up ℤ)).app K

/-- c_C is the mixed-tensor universal counit, transported to L by the unique universal
comparison, then identified with C/tC. In particular C is not assumed K-flat.
Source: Stacks 06Y6 (blueprint: lem-pod-derived-reduction-sheaf-resolution-independence). -/
noncomputable def c (K : CochainComplex (ModuleCat.{r} R) ℤ) :
    D.L.obj (DerivedCategory.Q.obj K) ⟶ DerivedCategory.Q.obj
      (((ModuleCat.extendScalars D.quotientMap).mapHomologicalComplex (.up ℤ)).obj K) :=
  (Functor.leftDerivedUnique D.pointwiseTensor D.L
    (D.tensorFamilyCounit D.quotientSingle) D.pointwiseCounit
    (HomologicalComplex.quasiIso (ModuleCat.{r} R) (.up ℤ))).hom.app
      (DerivedCategory.Q.obj K) ≫
    D.pointwiseCounit.app K ≫ DerivedCategory.Q.map (D.tensorSingleIso K).hom

set_option linter.unusedSectionVars false in
private theorem tensorSingleIso_naturality
    {K K' : CochainComplex (ModuleCat.{r} R) ℤ} (f : K ⟶ K') :
    (((ModuleCat.mixedTensor D.quotientMap).flip.map₂CochainComplex).map f).app
        D.quotientSingle ≫ (D.tensorSingleIso K').hom =
      (D.tensorSingleIso K).hom ≫
        ((ModuleCat.extendScalars D.quotientMap).mapHomologicalComplex (.up ℤ)).map f := by
  let e := CochainComplex.map₂HomologicalComplexFlipObjSingleIso
      (ModuleCat.mixedTensor D.quotientMap).flip (𝟙_ (ModuleCat.{r} D.A)) ≪≫
    NatIso.mapHomologicalComplex
      (isoWhiskerLeft (ModuleCat.extendScalars D.quotientMap)
        (leftUnitorNatIso (ModuleCat.{r} D.A)) ≪≫ Functor.rightUnitor _) (.up ℤ)
  dsimp only [tensorSingleIso]
  exact e.hom.naturality f

attribute [local irreducible] tensorSingleIso

private theorem c_naturality
    {K K' : CochainComplex (ModuleCat.{r} R) ℤ} (f : K ⟶ K') :
    D.c K ≫ DerivedCategory.Q.map
        (((ModuleCat.extendScalars D.quotientMap).mapHomologicalComplex (.up ℤ)).map f) =
      D.L.map (DerivedCategory.Q.map f) ≫ D.c K' := by
  let e := Functor.leftDerivedUnique D.pointwiseTensor D.L
    (D.tensorFamilyCounit D.quotientSingle) D.pointwiseCounit
    (HomologicalComplex.quasiIso (ModuleCat.{r} R) (.up ℤ))
  have hn := D.pointwiseCounit.naturality f
  have he := e.hom.naturality (DerivedCategory.Q.map f)
  dsimp only [c]
  simp only [Category.assoc]
  dsimp only [Functor.comp_map, Functor.flip_obj_map] at hn
  rw [ ← DerivedCategory.Q.map_comp,
    ← tensorSingleIso_naturality D f, DerivedCategory.Q.map_comp,
    ← Category.assoc (D.pointwiseCounit.app K), ← hn,
    ← Category.assoc]
  simp only [Category.assoc]
  rw [← Category.assoc (e.hom.app _) (D.pointwiseTensor.map _) _, ← he]
  simp only [Category.assoc]
  rfl

set_option backward.isDefEq.respectTransparency false

/-- The quotient image of a section, constructed by the module-sheafification unit.
Source: Stacks 03EK (blueprint: lem-pod-derived-reduction-sheaf-resolution-independence). -/
noncomputable def quotientSection
    (M : ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.O))
    (x : M.val.obj (op D.U)) : (D.extension.E.obj M).val.obj (op D.U) :=
  ((eqToHom (D.extension.obj_eq M).symm).val.app (op D.U))
    ((((PresheafOfModules.sheafificationAdjunction
      (R := derivedChangeRingIndependentCoefficients J D.S) (𝟙 _)).unit.app
        (changeOfRingsPresheaf D.φ M)).app (op D.U))
          ((1 : D.S.obj.obj (op D.U)) ⊗ₜ[D.O.obj.obj (op D.U),
            (D.φ.hom.app (op D.U)).hom] x))

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
private theorem quotientSection_naturality
    {M N : ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.O)}
    (f : M ⟶ N) (x : M.val.obj (op D.U)) :
    (D.extension.E.map f).val.app (op D.U) (D.quotientSection M x) =
      D.quotientSection N (f.val.app (op D.U) x) := by
  let g : changeOfRingsPresheaf D.φ M ⟶ changeOfRingsPresheaf D.φ N :=
    { app := fun V ↦ (ModuleCat.extendScalars (D.φ.hom.app V).hom).map (f.val.app V)
      naturality := changeOfRingsHom_naturality D.φ M f }
  have h := congrArg (fun k ↦ (k.app (op D.U))
    ((1 : D.S.obj.obj (op D.U)) ⊗ₜ[D.O.obj.obj (op D.U),
      (D.φ.hom.app (op D.U)).hom] x))
    ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (derivedChangeRingIndependentCoefficients J D.S).obj)).unit.naturality g)
  dsimp only [quotientSection]
  rw [D.extension.map_eq]
  simp only [comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  have he (z : (changeOfRings D.φ M).val.obj (op D.U)) :
      (eqToHom (D.extension.obj_eq M)).val.app (op D.U)
        ((eqToHom (D.extension.obj_eq M).symm).val.app (op D.U) z) = z := by
    have hc := congrArg (fun k ↦ k.val.app (op D.U))
      (show eqToHom (D.extension.obj_eq M).symm ≫
        eqToHom (D.extension.obj_eq M) = 𝟙 _ by simp)
    exact ConcreteCategory.congr_hom hc z
  rw [he]
  apply congrArg ((eqToHom (D.extension.obj_eq N).symm).val.app (op D.U))
  change ((PresheafOfModules.sheafification
      (𝟙 (derivedChangeRingIndependentCoefficients J D.S).obj)).map g).val.app
      (op D.U) _ = _
  change ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (derivedChangeRingIndependentCoefficients J D.S).obj)).unit.app
      (changeOfRingsPresheaf D.φ N)).app (op D.U)
        ((ModuleCat.extendScalars (D.φ.hom.app (op D.U)).hom).map
          (f.val.app (op D.U))
          ((1 : D.S.obj.obj (op D.U)) ⊗ₜ[D.O.obj.obj (op D.U),
            (D.φ.hom.app (op D.U)).hom] x)) = _ at h
  rw [ModuleCat.ExtendScalars.map_tmul] at h
  exact h.symm

set_option backward.isDefEq.respectTransparency false

private noncomputable def quotientSectionsHom
    (M : ringedSiteModules.{r} D.Omod) :
    D.sections.obj M ⟶ (ModuleCat.restrictScalars D.quotientMap).obj
      (D.quotientSections.obj (D.extension.E.obj M)) := by
  let e := (eqToHom (D.extension.obj_eq M).symm).val.app (op D.U)
  let f := (D.quotientMorphism M).val.app (op D.U)
  refine ModuleCat.ofHom (X := D.sections.obj M)
    (Y := (ModuleCat.restrictScalars D.quotientMap).obj
      (D.quotientSections.obj (D.extension.E.obj M)))
    { toFun := fun x ↦ e (f x)
      map_add' := fun x y ↦ by rw [_root_.map_add, _root_.map_add]
      map_smul' := ?_ }
  intro r x
  have h := f.hom.map_smul (D.ρ r) (show M.val.obj (op D.U) from x)
  change f (D.ρ r • (show M.val.obj (op D.U) from x)) =
    (D.φ.hom.app (op D.U)) (D.ρ r) •
      (show (changeOfRings D.φ M).val.obj (op D.U) from f x) at h
  change e (f (D.ρ r • (show M.val.obj (op D.U) from x))) =
    D.quotientSectionsMap (D.quotientMap r) • e (f x)
  rw [h, D.quotient_sections_comm]
  exact e.hom.map_smul _ _

private theorem quotientSectionsHom_apply
    (M : ringedSiteModules.{r} D.Omod) (x : M.val.obj (op D.U)) :
    D.quotientSectionsHom M x = D.quotientSection M x := by
  change (eqToHom (D.extension.obj_eq M).symm).val.app (op D.U)
    ((D.quotientMorphism M).val.app (op D.U) x) = _
  rw [D.quotientMorphism_apply]
  rfl

private noncomputable def quotientSectionsTensorHom
    (M : ringedSiteModules.{r} D.Omod) :
    (ModuleCat.extendScalars D.quotientMap).obj (D.sections.obj M) ⟶
      D.quotientSections.obj (D.extension.E.obj M) :=
  ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
    D.quotientMap (D.quotientSectionsHom M)

private theorem quotientSectionsTensorHom_tmul
    (M : ringedSiteModules.{r} D.Omod) (a : D.A) (x : M.val.obj (op D.U)) :
    D.quotientSectionsTensorHom M (a ⊗ₜ[R, D.quotientMap] x) =
      D.quotientSectionsMap a • D.quotientSection M x := by
  change D.quotientSectionsMap a •
    (show (D.extension.E.obj M).val.obj (op D.U) from D.quotientSectionsHom M x) = _
  rw [quotientSectionsHom_apply]

private theorem quotientSection_exact
    (M : ringedSiteModules.{r} D.Omod) (hf : IsFlatOnSite (R := D.O) M) :
    Function.Surjective (D.quotientSection M) ∧
      (∀ x : D.sections.obj M, D.quotientSection M x = 0 →
        ∃ y : D.sections.obj M, D.t • y = x) := by
  have : PreservesFiniteColimits D.sections := D.sectionsColimits
  have : PreservesFiniteLimits D.sections := D.sectionsLimits
  have hs := (D.tensorShortComplex_shortExact M hf).map_of_exact D.sections
  dsimp only [tensorShortComplex, ShortComplex.map] at hs
  have hsur := hs.moduleCat_surjective_g
  have hker := (ShortComplex.moduleCat_exact_iff _).1 hs.exact
  constructor
  · intro z
    let e := (D.quotientSections.obj
      (D.extension.E.obj M))
    let y := (eqToHom (D.extension.obj_eq M)).val.app (op D.U) z
    obtain ⟨x, hx⟩ := hsur y
    refine ⟨x, ?_⟩
    change (D.quotientMorphism M).val.app (op D.U) x = y at hx
    rw [D.quotientMorphism_apply] at hx
    dsimp only [quotientSection]
    erw [hx]
    have h := congrArg (fun g ↦ g.val.app (op D.U) z)
      (show eqToHom (D.extension.obj_eq M) ≫
        eqToHom (D.extension.obj_eq M).symm = 𝟙 _ by simp)
    exact h
  · intro x hx
    have hz : (D.quotientMorphism M).val.app (op D.U) x = 0 := by
      rw [D.quotientMorphism_apply]
      have h := congrArg ((eqToHom (D.extension.obj_eq M)).val.app (op D.U)) hx
      dsimp only [quotientSection] at h
      have he := congrArg (fun g ↦ g.val.app (op D.U))
        (show eqToHom (D.extension.obj_eq M).symm ≫
          eqToHom (D.extension.obj_eq M) = 𝟙 _ by simp)
      simp only [← ModuleCat.comp_apply, ← PresheafOfModules.comp_app, ← comp_val,
        he, id_val, PresheafOfModules.id_app, ModuleCat.id_apply, map_zero] at h
      exact h
    obtain ⟨y, hy⟩ := hker x hz
    refine ⟨y, ?_⟩
    change (D.tensorMultiplication M).val.app (op D.U) y = x at hy
    rw [D.tensorMultiplication_apply,
      D.terminal.hom_ext (D.terminal.from D.U) (𝟙 D.U)] at hy
    change D.ρ D.t • (show M.val.obj (op D.U) from y) =
      (show M.val.obj (op D.U) from x)
    simpa using hy

private theorem quotientSectionsTensorHom_isIso
    (M : ringedSiteModules.{r} D.Omod) (hf : IsFlatOnSite (R := D.O) M) :
    IsIso (D.quotientSectionsTensorHom M) := by
  apply (ConcreteCategory.isIso_iff_bijective _).2
  apply D.quotientTensor_bijective
  · intro z
    obtain ⟨x, hx⟩ := (D.quotientSection_exact M hf).1 z
    refine ⟨x, ?_⟩
    exact (D.quotientSectionsTensorHom_tmul M 1 x).trans
      (by simpa only [map_one, one_smul] using hx)
  · intro x hx
    have hx' := (D.quotientSectionsTensorHom_tmul M 1 x).symm.trans hx
    simp only [map_one, one_smul] at hx'
    exact (D.quotientSection_exact M hf).2 x hx'

/-- The exact-sections quotient identification is uniquely fixed by its section formula.
Source: Stacks 03EK, 03ER, 06YY
(blueprint: lem-pod-derived-reduction-sheaf-resolution-independence).
Proof: tensor the coefficient short exact sequence with each flat term of P.
Its cokernel is both P^i/tP^i and P^i tensor_O S, via x tensor b-bar to bx modulo t
and x-bar to x tensor 1. Exact sections identify its section cokernel with
Gamma(P^i)/tGamma(P^i). This gives the displayed bijective A-linear map on tensors.
The formula commutes with differentials, hence gives a complex isomorphism. Tensors
1 tensor x generate over A in every degree; the formula determines the chain map
uniquely, hence also its inverse and the entire isomorphism. -/
theorem existsUnique_theta
    (P : CochainComplex
      (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.O)) ℤ)
    (hflat : ∀ i : ℤ, IsFlatOnSite (R := D.O) (P.X i)) :
    ∃! e : ((ModuleCat.extendScalars D.quotientMap).mapHomologicalComplex (.up ℤ)).obj
        ((D.sections.mapHomologicalComplex (.up ℤ)).obj P) ≅
      (D.quotientSections.mapHomologicalComplex (.up ℤ)).obj (D.quotientComplex.obj P),
      ∀ (i : ℤ) (a : D.A) (x : (P.X i).val.obj (op D.U)),
        e.hom.f i (a ⊗ₜ[R, D.quotientMap] x) =
          D.quotientSectionsMap a • D.quotientSection (P.X i) x := by
  let e (i : ℤ) := D.quotientSectionsTensorHom (P.X i)
  have he (i : ℤ) : IsIso (e i) := D.quotientSectionsTensorHom_isIso (P.X i) (hflat i)
  have hc (i j : ℤ) :
      e i ≫ D.quotientSections.map (D.extension.E.map (P.d i j)) =
        (ModuleCat.extendScalars D.quotientMap).map (D.sections.map (P.d i j)) ≫ e j := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro x
    change D.quotientSections.map (D.extension.E.map (P.d i j))
        (e i ((1 : D.A) ⊗ₜ[R, D.quotientMap] x)) =
      e j ((ModuleCat.extendScalars D.quotientMap).map (D.sections.map (P.d i j))
        ((1 : D.A) ⊗ₜ[R, D.quotientMap] x))
    simp only [e, D.quotientSectionsTensorHom_tmul, map_one, one_smul,
      ModuleCat.ExtendScalars.map_tmul]
    exact D.quotientSection_naturality (P.d i j) x
  let E : ((ModuleCat.extendScalars D.quotientMap).mapHomologicalComplex (.up ℤ)).obj
      ((D.sections.mapHomologicalComplex (.up ℤ)).obj P) ≅
      (D.quotientSections.mapHomologicalComplex (.up ℤ)).obj (D.quotientComplex.obj P) :=
    HomologicalComplex.Hom.isoOfComponents (fun i ↦ asIso (e i))
      (fun i j _ ↦ hc i j)
  refine ⟨E, fun i a x ↦ D.quotientSectionsTensorHom_tmul (P.X i) a x, ?_⟩
  intro E' hE'
  apply Iso.ext
  ext i : 1
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  exact (hE' i 1 x).trans (D.quotientSectionsTensorHom_tmul (P.X i) 1 x).symm

set_option backward.isDefEq.respectTransparency true

/-- theta_P, chosen from a property that determines the whole isomorphism uniquely.
Source: Stacks 03EK, 06YY
(blueprint: lem-pod-derived-reduction-sheaf-resolution-independence). -/
noncomputable def theta
    (P : CochainComplex
      (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.O)) ℤ)
    (hflat : ∀ i : ℤ, IsFlatOnSite (R := D.O) (P.X i)) :=
  (existsUnique_theta D P hflat).exists.choose

set_option backward.isDefEq.respectTransparency false in
private theorem theta_naturality
    {P P' : CochainComplex
      (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.O)) ℤ}
    (hf : ∀ i : ℤ, IsFlatOnSite (R := D.O) (P.X i))
    (hf' : ∀ i : ℤ, IsFlatOnSite (R := D.O) (P'.X i)) (f : P ⟶ P') :
    ((ModuleCat.extendScalars D.quotientMap).mapHomologicalComplex (.up ℤ)).map
        ((D.sections.mapHomologicalComplex (.up ℤ)).map f) ≫ (D.theta P' hf').hom =
      (D.theta P hf).hom ≫ (D.quotientSections.mapHomologicalComplex (.up ℤ)).map
        (D.quotientComplex.map f) := by
  have ht := (existsUnique_theta D P hf).exists.choose_spec
  have ht' := (existsUnique_theta D P' hf').exists.choose_spec
  ext i : 1
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  change (D.theta P' hf').hom.f i
      ((ModuleCat.extendScalars D.quotientMap).map (D.sections.map (f.f i))
        ((1 : D.A) ⊗ₜ[R, D.quotientMap] x)) =
    D.quotientSections.map (D.extension.E.map (f.f i))
      ((D.theta P hf).hom.f i ((1 : D.A) ⊗ₜ[R, D.quotientMap] x))
  rw [ModuleCat.ExtendScalars.map_tmul]
  change (D.theta P' hf').hom.f i
      ((1 : D.A) ⊗ₜ[R, D.quotientMap] (f.f i).val.app (op D.U) x) = _
  rw [show (D.theta P' hf').hom.f i _ = _ from ht' i 1 _,
    show (D.theta P hf).hom.f i _ = _ from ht i 1 x]
  simp only [map_one, one_smul]
  exact (quotientSection_naturality D (f.f i) x).symm

/-- The canonical K-flat computation e_P is precisely the derived-extension counit.
Source: Stacks 06YY (blueprint: lem-pod-derived-reduction-sheaf-resolution-independence). -/
noncomputable def modelIso
    (P : CochainComplex
      (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.O)) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := D.O) P) :
    D.T.obj (DerivedCategory.Q.obj P) ≅ DerivedCategory.Q.obj (D.quotientComplex.obj P) :=
  letI := D.extension.computes P hP
  asIso (D.extension.ε.app P)

/-- alpha_P is theta_P after c_Gamma(P), with the localization factors and the inverse
of the canonical K-flat computation written explicitly. Source: Stacks 06YY, 06Y6
(blueprint: lem-pod-derived-reduction-sheaf-resolution-independence). -/
noncomputable def alpha
    (P : CochainComplex
      (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.O)) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := D.O) P)
    (hflat : ∀ i : ℤ, IsFlatOnSite (R := D.O) (P.X i)) :
    D.L.obj (D.G.obj (DerivedCategory.Q.obj P)) ⟶
      D.G'.obj (D.T.obj (DerivedCategory.Q.obj P)) :=
  D.L.map (D.sections.mapDerivedCategoryFactors.hom.app P) ≫
    D.c ((D.sections.mapHomologicalComplex (.up ℤ)).obj P) ≫
    DerivedCategory.Q.map (D.theta P hflat).hom ≫
    D.quotientSections.mapDerivedCategoryFactors.inv.app (D.quotientComplex.obj P) ≫
    D.G'.map (D.modelIso P hP).inv

private theorem alpha_naturality
    {P P' : CochainComplex
      (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.O)) ℤ}
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := D.O) P)
    (hP' : CochainComplex.IsKFlatIndependentCoefficients (R := D.O) P')
    (hf : ∀ i : ℤ, IsFlatOnSite (R := D.O) (P.X i))
    (hf' : ∀ i : ℤ, IsFlatOnSite (R := D.O) (P'.X i)) (f : P ⟶ P') :
    D.alpha P hP hf ≫ (D.T ⋙ D.G').map (DerivedCategory.Q.map f) =
      (D.G ⋙ D.L).map (DerivedCategory.Q.map f) ≫ D.alpha P' hP' hf' := by
  let s := D.sections.mapDerivedCategoryFactors
  let s' := D.quotientSections.mapDerivedCategoryFactors
  have hs := congrArg D.L.map (s.hom.naturality f)
  have hc := c_naturality D ((D.sections.mapHomologicalComplex (.up ℤ)).map f)
  have ht := congrArg DerivedCategory.Q.map (theta_naturality D hf hf' f)
  have hs' := s'.inv.naturality (D.quotientComplex.map f)
  have hm := D.extension.ε.naturality f
  have hi : (D.modelIso P hP).inv ≫ D.T.map (DerivedCategory.Q.map f) =
      DerivedCategory.Q.map (D.quotientComplex.map f) ≫ (D.modelIso P' hP').inv := by
    apply (cancel_epi (D.modelIso P hP).hom).1
    apply (cancel_mono (D.modelIso P' hP').hom).1
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id]
    exact hm
  have hi' := congrArg D.G'.map hi
  simp only [Functor.map_comp, Functor.comp_map] at hs ht hs' hi' ⊢
  dsimp only [alpha]
  calc
    _ = D.L.map (s.hom.app P) ≫
        D.c ((D.sections.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map (D.theta P hf).hom ≫
        DerivedCategory.Q.map
          ((D.quotientSections.mapHomologicalComplex (.up ℤ)).map
            (D.quotientComplex.map f)) ≫
        s'.inv.app (D.quotientComplex.obj P') ≫ D.G'.map (D.modelIso P' hP').inv := by
      simp only [Category.assoc]
      rw [← D.G'.map_comp, hi, D.G'.map_comp, ← Category.assoc (s'.inv.app _), ← hs']
      simp only [Category.assoc]
      rfl
    _ = _ := by
      rw [← Category.assoc (DerivedCategory.Q.map (D.theta P hf).hom), ← ht]
      simp only [Category.assoc]
      rw [← Category.assoc (D.c _), hc]
      simp only [Category.assoc]
      rw [← Category.assoc (D.L.map _), ← hs]
      simp only [Category.assoc]
      rfl

/-- The comparison transported along a supplied resolution p, taking no inverse of alpha.
Source: Stacks 06YY (blueprint: lem-pod-derived-reduction-sheaf-resolution-independence). -/
noncomputable def resolvedComparison
    {M P : CochainComplex
      (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.O)) ℤ}
    (p : P ⟶ M) [QuasiIso p]
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := D.O) P)
    (hflat : ∀ i : ℤ, IsFlatOnSite (R := D.O) (P.X i)) :
    D.L.obj (D.G.obj (DerivedCategory.Q.obj M)) ⟶
      D.G'.obj (D.T.obj (DerivedCategory.Q.obj M)) :=
  (D.G ⋙ D.L).map (inv (DerivedCategory.Q.map p)) ≫
    D.alpha P hP hflat ≫ (D.T ⋙ D.G').map (DerivedCategory.Q.map p)

set_option linter.unusedSectionVars false in
private theorem common_refinement
    (M P P' : CochainComplex
      (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.O)) ℤ)
    (p : P ⟶ M) (p' : P' ⟶ M) [QuasiIso p] [QuasiIso p'] :
    ∃ (S : CochainComplex
        (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.O)) ℤ)
      (a : S ⟶ P) (b : S ⟶ P'),
      CochainComplex.IsKFlatIndependentCoefficients (R := D.O) S ∧
      (∀ i : ℤ, IsFlatOnSite (R := D.O) (S.X i)) ∧
      QuasiIso a ∧ QuasiIso b ∧
      DerivedCategory.Q.map (a ≫ p) = DerivedCategory.Q.map (b ≫ p') := by
  let A := ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.O)
  let H := HomotopyCategory.quotient A (.up ℤ)
  let W := HomotopyCategory.quasiIso A (.up ℤ)
  let φ : W.LeftFraction (H.obj P) (H.obj P') :=
    MorphismProperty.LeftFraction.mk (H.map p) (H.map p')
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff p').2 (inferInstance : QuasiIso p'))
  obtain ⟨ψ, hψ⟩ := φ.exists_rightFraction
  obtain ⟨N, a, ha, b, rfl⟩ := ψ.cases
  obtain ⟨N, rfl⟩ := HomotopyCategory.quotient_obj_surjective N
  obtain ⟨a, rfl⟩ := H.map_surjective a
  obtain ⟨b, rfl⟩ := H.map_surjective b
  have : QuasiIso a := (HomotopyCategory.quotient_map_mem_quasiIso_iff a).1 ha
  have h : Homotopy (a ≫ p) (b ≫ p') :=
    HomotopyCategory.homotopyOfEq _ _ (by simpa [φ, H] using hψ)
  have : QuasiIso (b ≫ p') := by
    rw [quasiIso_iff]
    intro i
    rw [quasiIsoAt_iff_isIso_homologyMap, ← h.homologyMap_eq]
    infer_instance
  have : QuasiIso b := quasiIso_of_comp_right b p'
  obtain ⟨S, q, hS, hfS, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := D.O) N
  have hfS' (i : ℤ) : IsFlatOnSite (R := D.O) (S.X i) :=
    (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso D.O (S.X i)).symm (hfS i)
  refine ⟨S, q ≫ a, q ≫ b, hS, hfS', inferInstance, inferInstance, ?_⟩
  exact DerivedCategory.Q_map_eq_of_homotopy _
    ((Homotopy.ofEq (Category.assoc _ _ _)).trans
      ((h.compLeft q).trans (Homotopy.ofEq (Category.assoc _ _ _).symm)))

private theorem resolvedComparison_refinement
    {M P S : CochainComplex
      (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.O)) ℤ}
    (p : P ⟶ M) (a : S ⟶ P) [QuasiIso p] [QuasiIso a]
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := D.O) P)
    (hS : CochainComplex.IsKFlatIndependentCoefficients (R := D.O) S)
    (hf : ∀ i : ℤ, IsFlatOnSite (R := D.O) (P.X i))
    (hfS : ∀ i : ℤ, IsFlatOnSite (R := D.O) (S.X i)) :
    D.resolvedComparison p hP hf = D.resolvedComparison (a ≫ p) hS hfS := by
  let F := D.G ⋙ D.L
  let H := D.T ⋙ D.G'
  have hn := alpha_naturality D hS hP hfS hf a
  change D.alpha S hS hfS ≫ H.map (DerivedCategory.Q.map a) =
    F.map (DerivedCategory.Q.map a) ≫ D.alpha P hP hf at hn
  dsimp only [resolvedComparison]
  change F.map (inv (DerivedCategory.Q.map p)) ≫ D.alpha P hP hf ≫
    H.map (DerivedCategory.Q.map p) =
    F.map (inv (DerivedCategory.Q.map (a ≫ p))) ≫ D.alpha S hS hfS ≫
      H.map (DerivedCategory.Q.map (a ≫ p))
  simp only [DerivedCategory.Q.map_comp, IsIso.inv_comp, F.map_comp, H.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc (D.alpha S hS hfS), hn]
  simp only [Category.assoc]
  rw [← Category.assoc (F.map (inv (DerivedCategory.Q.map a))),
    ← F.map_comp, IsIso.inv_hom_id, F.map_id, Category.id_comp]

/-- Naturality for every map between flat-term K-flat models, and independence of two
such resolutions of an arbitrary unbounded complex. Neither clause asserts invertibility
of alpha. Source: Stacks 06YY and the extracted homotopy-refinement argument
(blueprint: lem-pod-derived-reduction-sheaf-resolution-independence).

Proof (the six steps of the node):
1. Exact abelian sections preserve kernels and cokernels, hence cohomology. Restricting
scalars changes no underlying group, so G and G' descend through quasi-isomorphisms.
2. Flat terms and the coefficient sequence identify P tensor S with P/tP. Exact sections
give theta_P. On the class of x, both maps in its naturality square give the class of h(x).
3. Specialize the mixed-tensor counit to A[0]. Its naturality and the natural ordinary
quotient identification give Q_A(u-bar) c_C = c_C' L(Q_R u), for arbitrary section C.
4. The K-flat computation e_P is the sheaf extension counit, so it too is natural in h.
Combine its square with steps 2 and 3 and conjugate by G'(e_P) to get the first clause.
5. The calculus of fractions in the homotopy category gives a common refinement N
of the two quasi-isomorphisms, commuting up to homotopy. Resolve N by a flat-term
K-flat S. The two maps S to P and P' are quasi-isomorphisms, and their composites
with p and p' become equal after localization.
6. Write F=LG, H=G'T and beta(p)=F(p)^(-1) alpha_P H(p), in Lean composition order.
Naturality for a:S->P and cancellation of F(a) give beta(p)=beta(ap).
The same argument gives beta(p')=beta(bp'). The two localized composites are equal,
so the transported comparisons agree. All inverses are images of resolution maps
or K-flat counits;
no inverse of alpha is used. Thus the equality uses exactly the canonical model
identifications specified by the supplied resolutions. -/
theorem resolution_independence :
    (∀ (P P' : CochainComplex
        (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.O)) ℤ)
      (hP : CochainComplex.IsKFlatIndependentCoefficients (R := D.O) P)
      (hP' : CochainComplex.IsKFlatIndependentCoefficients (R := D.O) P')
      (hf : ∀ i : ℤ, IsFlatOnSite (R := D.O) (P.X i))
      (hf' : ∀ i : ℤ, IsFlatOnSite (R := D.O) (P'.X i)) (h : P ⟶ P'),
      D.alpha P hP hf ≫ (D.T ⋙ D.G').map (DerivedCategory.Q.map h) =
        (D.G ⋙ D.L).map (DerivedCategory.Q.map h) ≫ D.alpha P' hP' hf') ∧
    (∀ (M P P' : CochainComplex
        (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.O)) ℤ)
      (p : P ⟶ M) (p' : P' ⟶ M) [QuasiIso p] [QuasiIso p']
      (hP : CochainComplex.IsKFlatIndependentCoefficients (R := D.O) P)
      (hP' : CochainComplex.IsKFlatIndependentCoefficients (R := D.O) P')
      (hf : ∀ i : ℤ, IsFlatOnSite (R := D.O) (P.X i))
      (hf' : ∀ i : ℤ, IsFlatOnSite (R := D.O) (P'.X i)),
      D.resolvedComparison p hP hf = D.resolvedComparison p' hP' hf') := by
  refine ⟨fun P P' hP hP' hf hf' h ↦ alpha_naturality D hP hP' hf hf' h, ?_⟩
  intro M P P' p p' hp hp' hP hP' hf hf'
  obtain ⟨S, a, b, hS, hfS, ha, hb, heq⟩ := common_refinement D M P P' p p'
  rw [resolvedComparison_refinement D p a hP hS hf hfS,
    resolvedComparison_refinement D p' b hP' hS hf' hfS]
  dsimp only [resolvedComparison]
  simp only [heq]

end Setup
end PrincipalReduction
end SheafOfModules
