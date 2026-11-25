/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
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
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
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
public import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteZerothHypercohomologyOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Adjunction.Basic
import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
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
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory

public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.CategoryTheory.SmoothPurity.HomComplexGlobalHomotopyOfUniverses
import WeilConjectures.Algebra.Homology.KInjectiveHomComplexOfUniverses
import WeilConjectures.Algebra.Homology.HomComplex
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import WeilConjectures.Algebra.Homology.HomTensorDegreewiseIso
import WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.Algebra.Homology.InternalHom
import WeilConjectures.Algebra.Homology.HomComplexComponents
import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import Mathlib.Algebra.Category.Grp.Abelian
import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
import WeilConjectures.Algebra.Homology.HomComplexProjections
import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import Mathlib.Algebra.Category.Grp.EpiMono
import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Homology.Functor
/-! # K-injective models for internal Hom and its derived global sections

Source: Stacks Project, sites-cohomology.tex, Section 08J7 (section-internal-hom),
Lemmas 0A95, 0A96, 08JA and 08J9
(blueprint: lem-sfb-derived-internal-hom-sections-model).

The tensor functor is characterized by its natural total-complex models on K-flat
representatives. The internal Hom is the existing Hom-complex localization. All
representative comparisons are natural isomorphisms, including the full derived
complex of global sections, rather than only its zeroth cohomology.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe c v r w z

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace CategoryTheory.DerivedInternalHomSectionsModel

set_option backward.isDefEq.respectTransparency false in
open CochainComplex HomComplex Preadditive in
private noncomputable def precompHomologyData
    {D : Type*} [Category* D] [Preadditive D]
    {A A' B : CochainComplex D ℤ} (f : A' ⟶ A) (n : ℤ) :
    ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor _ _ n).map
        (CategoryTheory.externalMap f (𝟙 B)))
      (HomComplex.leftHomologyData A B n) (HomComplex.leftHomologyData A' B n) where
  φK := AddCommGrpCat.ofHom
    { toFun := fun z ↦ z.precomp f
      map_zero' := by ext; simp
      map_add' := by intros; ext; simp }
  φH := (CohomologyClass.homAddEquiv (K := A) (L := B) (n := n)).toAddCommGrpIso.hom ≫
    (AddCommGrpCat.ofHom
      { toFun := fun a ↦ (HomotopyCategory.quotient D (.up ℤ)).map f ≫ a
        map_zero' := by simp
        map_add' := by intros; simp [comp_add] }) ≫
      (CohomologyClass.homAddEquiv (K := A') (L := B) (n := n)).toAddCommGrpIso.inv
  commi := by
    ext z
    change (z.precomp f).1 = (CategoryTheory.externalMap f (𝟙 B)).f n z.1
    simp [CategoryTheory.externalMap, Cocycle.precomp]
  commf' := by
    rw [← cancel_mono (HomComplex.leftHomologyData A' B n).i]
    simp only [Category.assoc, ShortComplex.LeftHomologyData.f'_i]
    have hi : AddCommGrpCat.ofHom
        { toFun := fun z : Cocycle A B n ↦ z.precomp f
          map_zero' := by ext; simp
          map_add' := by intros; ext; simp } ≫
        (HomComplex.leftHomologyData A' B n).i =
      (HomComplex.leftHomologyData A B n).i ≫
        (CategoryTheory.externalMap f (𝟙 B)).f n := by
      ext z
      change (z.precomp f).1 = (CategoryTheory.externalMap f (𝟙 B)).f n z.1
      simp [CategoryTheory.externalMap, Cocycle.precomp]
    rw [hi, ShortComplex.LeftHomologyData.f'_i_assoc]
    exact ((HomologicalComplex.shortComplexFunctor _ _ n).map
      (CategoryTheory.externalMap f (𝟙 B))).comm₁₂.symm
  commπ := by
    ext z
    apply (CohomologyClass.homAddEquiv (K := A') (L := B) (n := n)).injective
    change (CohomologyClass.homAddEquiv (K := A') (L := B) (n := n))
      ((CohomologyClass.homAddEquiv (K := A') (L := B) (n := n)).symm
        ((HomotopyCategory.quotient D (.up ℤ)).map f ≫
          CohomologyClass.toHom (CohomologyClass.mk z))) =
      CohomologyClass.toHom (CohomologyClass.mk (z.precomp f))
    rw [AddEquiv.apply_symm_apply, CohomologyClass.toHom_mk,
      CohomologyClass.toHom_mk, ← Functor.map_comp]
    congr 1
    ext p
    simp [Cocycle.equivHomShift_symm_apply, Cocycle.homOf, Cocycle.rightShift,
      Cochain.rightShift_v, Cocycle.precomp, Cochain.zero_cochain_comp_v]

private theorem bijective_precomp_quotient
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    {K L T : CochainComplex A ℤ} (t : K ⟶ L) [QuasiIso t] [T.IsKInjective] :
    Function.Bijective (fun f :
      (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L ⟶
        (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj T ↦
      (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map t ≫ f) := by
  let q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  let a := DerivedCategory.Qh.map (q.map t)
  have ha : IsIso a := by
    change IsIso ((q ⋙ DerivedCategory.Qh).map t)
    exact (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso A) t).2 inferInstance
  have hK := CochainComplex.IsKInjective.Qh_map_bijective (q.obj K) T
  have hL := CochainComplex.IsKInjective.Qh_map_bijective (q.obj L) T
  constructor
  · intro f g h
    apply hL.injective
    apply (cancel_epi a).mp
    change DerivedCategory.Qh.map (q.map t) ≫ _ = _
    simpa only [a, q, Functor.map_comp] using congrArg DerivedCategory.Qh.map h
  · intro g
    obtain ⟨f, hf⟩ := hL.surjective (inv a ≫ DerivedCategory.Qh.map g)
    refine ⟨f, hK.injective ?_⟩
    rw [Functor.map_comp, hf]
    exact IsIso.hom_inv_id_assoc a _

set_option backward.isDefEq.respectTransparency false in
private theorem externalMap_quasiIso
    {D : Type*} [Category* D] [Abelian D] [HasDerivedCategory D]
    {A A' B : CochainComplex D ℤ} (f : A' ⟶ A) [QuasiIso f] [B.IsKInjective] :
    QuasiIso (CategoryTheory.externalMap f (𝟙 B)) := by
  refine ⟨fun n ↦ ?_⟩
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have h := (precompHomologyData (B := B) f n).homologyMap_eq
  change HomologicalComplex.homologyMap (CategoryTheory.externalMap f (𝟙 B)) n = _ at h
  rw [h]
  have hpre : IsIso (AddCommGrpCat.ofHom
      { toFun := fun a :
          (HomotopyCategory.quotient D (.up ℤ)).obj A ⟶
            (HomotopyCategory.quotient D (.up ℤ)).obj (B⟦n⟧) ↦
          (HomotopyCategory.quotient D (.up ℤ)).map f ≫ a
        map_zero' := by simp
        map_add' := by intros; simp [Preadditive.comp_add] }) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact bijective_precomp_quotient (T := B⟦n⟧) f
  dsimp only [precompHomologyData]
  infer_instance

open CochainComplex HomComplex in
private noncomputable def externalDerivedEquiv
    {D : Type*} [Category* D] [Abelian D] [HasDerivedCategory D]
    (A I : CochainComplex D ℤ) [I.IsKInjective] (n : ℤ) :
    (HomComplex A I).homology n ≃+
      (DerivedCategory.Q.obj A ⟶ (DerivedCategory.Q.obj I)⟦n⟧) :=
  (HomComplex.homologyAddEquiv A I n).trans
    ((CohomologyClass.homAddEquiv (K := A) (L := I) (n := n)).trans
      ((AddEquiv.ofBijective DerivedCategory.Qh.mapAddHom
        (IsKInjective.Qh_map_bijective _ (I⟦n⟧))).trans
        (Linear.homCongr ℤ ((DerivedCategory.quotientCompQhIso D).app A)
          ((DerivedCategory.quotientCompQhIso D).app (I⟦n⟧) ≪≫
            (DerivedCategory.Q.commShiftIso n).app I)).toAddEquiv))

private noncomputable def sectionsComparison
    {D E : Type*} [Category* D] [Category* E] [Abelian D] [Abelian E]
    [HasDerivedCategory D] [HasDerivedCategory E]
    [Abelian.HasKInjectiveResolutions D] (F : D ⥤ E) [F.Additive] :
    F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ F.rightDerivedFunctor :=
  (Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors (.up ℤ)) DerivedCategory.Qh ≪≫
    Functor.isoWhiskerLeft (F.mapHomologicalComplex (.up ℤ))
      (DerivedCategory.quotientCompQhIso E)).inv ≫
    Functor.whiskerLeft (HomotopyCategory.quotient D (.up ℤ)) F.rightDerivedFunctorUnit ≫
      (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso D)
        F.rightDerivedFunctor).hom

private theorem isIso_sectionsComparison
    {D E : Type*} [Category* D] [Category* E] [Abelian D] [Abelian E]
    [HasDerivedCategory D] [HasDerivedCategory E]
    [Abelian.HasKInjectiveResolutions D] (F : D ⥤ E) [F.Additive]
    (T : CochainComplex D ℤ) [T.IsKInjective] :
    IsIso ((sectionsComparison F).app T) := by
  dsimp [sectionsComparison]
  infer_instance

attribute [local irreducible] sectionsComparison Functor.rightDerivedFunctor
  Functor.rightDerivedFunctorUnit

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{max c v r})

/-- The recorded module category, with sections in a universe containing the site.
Source: Stacks, Section 08J7
(blueprint: lem-sfb-derived-internal-hom-sections-model). -/
abbrev Modules := ringedSiteModules.{max c v r}
  ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)

/-- Unbounded cochain complexes in the recorded module category.
Source: Stacks, Section 08J7
(blueprint: lem-sfb-derived-internal-hom-sections-model). -/
abbrev Complexes := CochainComplex (Modules.{c, v, r} R) ℤ

variable [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]

/-- The recorded unbounded derived category, with its chosen morphism universe.
Source: Stacks, Section 08J7
(blueprint: lem-sfb-derived-internal-hom-sections-model). -/
abbrev Derived [HasDerivedCategory.{w} (Modules.{c, v, r} R)] :=
  DerivedCategory (Modules.{c, v, r} R)

/-- Ordinary global sections are morphisms from the unit module sheaf.
Source: Stacks, Section 07A5 and Lemma 08JA
(blueprint: lem-sfb-derived-internal-hom-sections-model). -/
noncomputable abbrev sections : Modules.{c, v, r} R ⥤ AddCommGrpCat.{max c v r} :=
  preadditiveCoyoneda.obj (op (SheafOfModules.unit
    ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)))

variable [HasDerivedCategory.{w} (Modules.{c, v, r} R)]
  [HasDerivedCategory.{z} AddCommGrpCat.{max c v r}]

/-- The full right derived global-sections functor underlying the recorded
zeroth-hypercohomology construction. It uses the same canonical K-injective replacement.
Source: Stacks, Section 07A5 and Lemma 08JA
(blueprint: lem-sfb-derived-internal-hom-sections-model). -/
noncomputable def derivedSections :
    Derived.{c, v, r, w} R ⥤ DerivedCategory.{z} AddCommGrpCat.{max c v r} :=
  letI : IsGrothendieckAbelian.{max c v r} (Modules.{c, v, r} R) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, r}
      J R).1
  (sections.{c, v, r} R).rightDerivedFunctor

/-- The existing internal-Hom bifunctor, in curried form.
Source: Stacks, Section 08J7
(blueprint: lem-sfb-derived-internal-hom-sections-model). -/
noncomputable abbrev internalHom :
    (Derived.{c, v, r, w} R)ᵒᵖ ⥤ Derived.{c, v, r, w} R ⥤ Derived.{c, v, r, w} R :=
  Functor.curry.obj (derivedInternalHomOfUniverses.{c, v, r, w} J R)

/-- The full subcategory of K-injective complexes; no condition on the source is imposed.
Source: Stacks, Definition 070H and Section 08J7
(blueprint: lem-sfb-derived-internal-hom-sections-model). -/
def injectiveProperty : ObjectProperty (Complexes.{c, v, r} R) :=
  fun I ↦ CochainComplex.IsKInjective I

/-- Restrict the recorded derived internal Hom to arbitrary source complexes and
K-injective target complexes.
Source: Stacks, Section 08J7
(blueprint: lem-sfb-derived-internal-hom-sections-model). -/
noncomputable def representedInternalHom :
    (Complexes.{c, v, r} R)ᵒᵖ × (injectiveProperty.{c, v, r} R).FullSubcategory ⥤
      Derived.{c, v, r, w} R :=
  (DerivedCategory.Q.op.prod ((injectiveProperty.{c, v, r} R).ι ⋙ DerivedCategory.Q)) ⋙
    derivedInternalHomOfUniverses.{c, v, r, w} J R

/-- The recorded sheaf Hom complex on the same pairs of representatives.
Source: Stacks, Section 08J7 and Section 0A8X
(blueprint: lem-sfb-derived-internal-hom-sections-model). -/
noncomputable def representativeHom :
    (Complexes.{c, v, r} R)ᵒᵖ × (injectiveProperty.{c, v, r} R).FullSubcategory ⥤
      Complexes.{c, v, r} R :=
  (𝟭 (Complexes.{c, v, r} R)ᵒᵖ).prod (injectiveProperty.{c, v, r} R).ι ⋙
    Functor.uncurry.obj (homComplexFunctor (R := R))

/-- The ordinary complex of global Hom cochains, functorially in both representatives.
Source: Stacks, Section 0A8X, equation-global-cohomology-hom-complex
(blueprint: lem-sfb-derived-internal-hom-sections-model). -/
noncomputable def globalHom :
    (Complexes.{c, v, r} R)ᵒᵖ × (injectiveProperty.{c, v, r} R).FullSubcategory ⥤
      CochainComplex AddCommGrpCat.{max c v r} ℤ :=
  representativeHom.{c, v, r} R ⋙ (sections.{c, v, r} R).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Total tensor complexes, using precisely the recorded sheaf tensor and Koszul signs.
Source: Stacks, Section 06YL and Section 08J7
(blueprint: lem-sfb-derived-internal-hom-sections-model). -/
noncomputable def totalTensor :
    Complexes.{c, v, r} R ⥤ Complexes.{c, v, r} R ⥤ Complexes.{c, v, r} R :=
  letI := (SheafOfModules.isMonoidal_W_independentCoefficients R)
  letI := SheafOfModules.monoidalCategory R
  letI := (SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R)
  letI := (SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R)
  (curriedTensor (Modules.{c, v, r} R)).map₂HomologicalComplex
    (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)

attribute [local irreducible] homComplexFunctor CategoryTheory.globalComplexIso

set_option backward.isDefEq.respectTransparency false in
omit [HasDerivedCategory.{z} AddCommGrpCat.{max c v r}] in
private theorem globalMap_quasiIso
    {A P I : Complexes.{c, v, r} R} (p : P ⟶ A) [QuasiIso p] [I.IsKInjective] :
    QuasiIso ((CategoryTheory.globalBifunctor.{c, v, r} R).map
      (X := (op A, I)) (Y := (op P, I)) (p.op, 𝟙 I)) := by
  have : QuasiIso (CategoryTheory.externalMap p (𝟙 I)) := externalMap_quasiIso p
  have h := CategoryTheory.globalComplexIso_naturality.{c, v, r} R p (𝟙 I)
  apply (quasiIso_iff_comp_right _ (CategoryTheory.globalComplexIso.{c, v, r}
    R (op P, I)).hom).mp
  rw [h]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
-- Naturality compares several composites through product functors and localization.
/-- Natural K-injective models for the internal Hom, its full derived global sections,
and all of its hypercohomology groups. The third comparison identifies the ordinary
sections complex with the usual global Hom complex, including its differential and
its degree-n product of morphism groups.

Source: Stacks, Section 08J7, Lemmas 08JA, 08J9, 0A95 and 0A96
(blueprint: lem-sfb-derived-internal-hom-sections-model).

Proof: First compare the canonical functorial K-injective replacement of I with I
itself. Its resolution map is a quasi-isomorphism between K-injectives. Applying
Hom(A,-) and Q inverts it by 0A95. The resulting comparison with the localized
internal Hom is natural in every source chain map and every map between K-injectives.
Next replace A by a K-flat P. Hom(P,I) is K-injective by 0A96, hence RΓ is computed
by ordinary sections on it. A quasi-isomorphism P to A induces quasi-isomorphisms
on both sheaf Hom complexes and global Hom complexes, since I is K-injective.
This transports the full-complex comparison back to A. Functorial resolutions and
naturality of pre- and postcomposition give the displayed natural isomorphism.
In each degree, sections commute with products and sections of sheaf Hom are global
module maps. These identifications give the third chain isomorphism: its differential
is d_I f - (-1)^n f d_A. The same component formula gives the naturality equation below.
Finally the cohomology of the global Hom complex is homotopy classes A to I[n].
K-injectivity identifies these with derived morphisms. Transport along representatives
of K and M gives the last assertion for every integer n, including negative n.
Zero complexes and the empty site are included; no boundedness or flatness of A is used. -/
theorem derived_internalHom_sections_model :
    Nonempty (representedInternalHom.{c, v, r, w} R ≅
      representativeHom.{c, v, r} R ⋙ DerivedCategory.Q) ∧
    Nonempty (representedInternalHom.{c, v, r, w} R ⋙ derivedSections.{c, v, r, w, z} R ≅
      globalHom.{c, v, r} R ⋙ DerivedCategory.Q) ∧
    (∃ e : ∀ (A I : Complexes.{c, v, r} R),
        ((sections.{c, v, r} R).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (homComplex (R := R) A I) ≅ CochainComplex.HomComplex A I,
      ∀ (A A' I I' : Complexes.{c, v, r} R) (f : A' ⟶ A) (g : I ⟶ I')
        (n p q : ℤ) (hpq : p + n = q)
        (s : (((sections.{c, v, r} R).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (homComplex (R := R) A I)).X n),
        ((e A' I').hom.f n
          ((((sections.{c, v, r} R).mapHomologicalComplex (ComplexShape.up ℤ)).map
            (((homComplexFunctor (R := R)).map f.op).app I ≫
              ((homComplexFunctor (R := R)).obj (op A')).map g)).f n s)).v p q hpq =
          f.f p ≫ ((e A I).hom.f n s).v p q hpq ≫ g.f q) ∧
    (∀ (K M : Derived.{c, v, r, w} R) (n : ℤ),
      Nonempty (((DerivedCategory.homologyFunctor.{z} AddCommGrpCat.{max c v r} n).obj
        ((derivedSections.{c, v, r, w, z} R).obj
          (((internalHom.{c, v, r, w} R).obj (op K)).obj M))) ≃+
          (K ⟶ M⟦n⟧))) := by
  classical
  let A := Modules.{c, v, r} R
  let : IsGrothendieckAbelian.{max c v r} A :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, r}
      J R).1
  let I := CochainComplex.kInjectiveResolutionFunctor.{max c v r} A
  let η := CochainComplex.toKInjectiveResolution.{max c v r} A
  let G := (𝟭 (Complexes.{c, v, r} R)ᵒᵖ).prod (injectiveProperty.{c, v, r} R).ι
  let H := Functor.uncurry.obj (homComplexFunctor (R := R))
  obtain ⟨e₀⟩ := derivedInternalHomOfUniverses_comparison.{c, v, r, w} J R I η (fun M ↦
    ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{max c v r} A M).2,
      CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{max c v r} A M⟩)
  let α := Functor.whiskerLeft G
    (Functor.whiskerRight (NatTrans.prod (𝟙 (𝟭 (Complexes.{c, v, r} R)ᵒᵖ)) η)
      (H ⋙ DerivedCategory.Q))
  have : IsIso α := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro X
    have : X.2.obj.IsKInjective := X.2.property
    have : (I.obj X.2.obj).IsKInjective :=
      CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{max c v r} A _
    have : QuasiIso (η.app X.2.obj) :=
      (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{max c v r} A _).2
    apply (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr
    exact quasiIso_homComplex_mapOfUniverses.{c, v, r}
      (I' := X.2.obj) (I := I.obj X.2.obj) (η.app X.2.obj) (𝟙 X.1.unop)
  let a : representedInternalHom.{c, v, r, w} R ≅
      representativeHom.{c, v, r} R ⋙ DerivedCategory.Q :=
    Functor.isoWhiskerLeft G e₀ ≪≫ (asIso α).symm
  have hb : Nonempty (representedInternalHom.{c, v, r, w} R ⋙
      derivedSections.{c, v, r, w, z} R ≅ globalHom.{c, v, r} R ⋙
        DerivedCategory.Q) := by
    let Γ := sections.{c, v, r} R
    let Gs := Γ.mapHomologicalComplex (.up ℤ)
    let δ := sectionsComparison Γ
    have hδ (T : Complexes.{c, v, r} R) [T.IsKInjective] : IsIso (δ.app T) :=
      isIso_sectionsComparison Γ T
    let F := representativeHom.{c, v, r} R
    let γ := Functor.whiskerLeft F δ
    have hγ : ∀ X, IsIso (γ.app X) := by
      rintro ⟨L, I'⟩
      have : I'.obj.IsKInjective := I'.property
      obtain ⟨P, p, hP, _, hp, _⟩ :=
        CochainComplex.exists_isKFlatResolutionIndependentCoefficients L.unop
      have : QuasiIso p := hp
      let f : (L, I') ⟶ (op P, I') := (p.op, 𝟙 I')
      have hflat : (homComplex (R := R) P I'.obj).IsKInjective :=
        CochainComplex.isKInjective_homComplex_of_isKFlatOfUniverses.{r, c, v} P I'.obj hP
      have hf : QuasiIso (F.map f) := by
        exact quasiIso_homComplex_mapOfUniverses.{c, v, r} (𝟙 I'.obj) p
      have : IsIso ((F ⋙ DerivedCategory.Q ⋙ Γ.rightDerivedFunctor).map f) := by
        change IsIso (Γ.rightDerivedFunctor.map (DerivedCategory.Q.map (F.map f)))
        infer_instance
      have : QuasiIso (Gs.map (F.map f)) := by
        change QuasiIso ((CategoryTheory.globalBifunctor.{c, v, r} R).map
          (X := (L, I'.obj)) (Y := (op P, I'.obj)) (p.op, 𝟙 I'.obj))
        exact globalMap_quasiIso R p
      have : IsIso ((F ⋙ Gs ⋙ DerivedCategory.Q).map f) := by
        change IsIso (DerivedCategory.Q.map (Gs.map (F.map f)))
        infer_instance
      have : IsIso (γ.app (op P, I')) := by
        change IsIso (δ.app (homComplex (R := R) P I'.obj))
        exact hδ _
      have hn := γ.naturality f
      have : IsIso (γ.app (L, I') ≫
          (F ⋙ DerivedCategory.Q ⋙ Γ.rightDerivedFunctor).map f) := by
        rw [← hn]
        infer_instance
      exact IsIso.of_isIso_comp_right _
        ((F ⋙ DerivedCategory.Q ⋙ Γ.rightDerivedFunctor).map f)
    have : IsIso γ := (NatTrans.isIso_iff_isIso_app γ).mpr hγ
    exact ⟨Functor.isoWhiskerRight a (derivedSections.{c, v, r, w, z} R) ≪≫
      (asIso γ).symm⟩
  refine ⟨⟨a⟩, hb, ?_, ?_⟩
  · refine ⟨fun A I ↦ CategoryTheory.globalComplexIso.{c, v, r} R (op A, I), ?_⟩
    intro A A' I I' f g n p q hpq s
    have hn := CategoryTheory.globalComplexIso_naturality.{c, v, r} R f g
    have hv := ConcreteCategory.congr_hom
      (congrArg (fun k ↦ k.f n) hn) s
    exact (congrArg (fun x ↦ x.v p q hpq) hv).trans
      (CategoryTheory.externalMap_v f g n _ p q hpq)
  · intro K M n
    let L := DerivedCategory.Q.objPreimage K
    let N := DerivedCategory.Q.objPreimage M
    let T := I.obj N
    have : T.IsKInjective :=
      CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{max c v r} A N
    have : QuasiIso (η.app N) :=
      (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{max c v r} A N).2
    let eL : DerivedCategory.Q.obj L ≅ K := DerivedCategory.Q.objObjPreimageIso K
    let eM : DerivedCategory.Q.obj T ≅ M :=
      (asIso (DerivedCategory.Q.map (η.app N))).symm ≪≫
        DerivedCategory.Q.objObjPreimageIso M
    let ii : (injectiveProperty.{c, v, r} R).FullSubcategory :=
      ⟨T, (show T.IsKInjective from inferInstance)⟩
    obtain ⟨b⟩ := hb
    let h : (((internalHom.{c, v, r, w} R).obj (op K)).obj M) ≅
        (representedInternalHom.{c, v, r, w} R).obj (op L, ii) :=
      (derivedInternalHomOfUniverses.{c, v, r, w} J R).mapIso (eL.op.prod eM.symm)
    let Hd := DerivedCategory.homologyFunctor.{z} AddCommGrpCat.{max c v r} n
    let hc := (derivedSections.{c, v, r, w, z} R).mapIso h ≪≫ b.app (op L, ii)
    let ht : Hd.obj ((derivedSections.{c, v, r, w, z} R).obj
          (((internalHom.{c, v, r, w} R).obj (op K)).obj M)) ≅
        (CochainComplex.HomComplex L T).homology n :=
      Hd.mapIso hc ≪≫
        (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{max c v r} n).app
          ((globalHom.{c, v, r} R).obj (op L, ii)) ≪≫
        (HomologicalComplex.homologyFunctor AddCommGrpCat.{max c v r} (.up ℤ) n).mapIso
          (CategoryTheory.globalComplexIso.{c, v, r} R (op L, T))
    exact ⟨(ht.addCommGroupIsoToAddEquiv).trans
      ((externalDerivedEquiv L T n).trans
        (Linear.homCongr ℤ eL ((shiftFunctor _ n).mapIso eM)).toAddEquiv)⟩

end CategoryTheory.DerivedInternalHomSectionsModel
