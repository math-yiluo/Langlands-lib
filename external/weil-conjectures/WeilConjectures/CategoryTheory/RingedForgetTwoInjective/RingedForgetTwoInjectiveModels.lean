/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
public import WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction
public import WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
public import WeilConjectures.Algebra.Homology.KInjectiveHomComplexOfUniverses
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomTensorDegreewiseIso
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.AdjunctionRingOperations
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic
public import WeilConjectures.CategoryTheory.GeometricModuleConstruction
public import WeilConjectures.CategoryTheory.RingedToposRingData
public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.GeometricModuleTransport
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import WeilConjectures.Algebra.Homology.InternalHom
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
public import WeilConjectures.Algebra.Homology.HomotopyCategory.InternalHom
public import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
public import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
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
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.WeilSheaf.DerivedHom
public import WeilConjectures.WeilSheaf.LowerShriek
public import WeilConjectures.CategoryTheory.TwistedActionRingedSite.TwistedActionRingedSite
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedCondensedCoefficients
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.IsoAlgebra
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
import WeilConjectures.Algebra.Homology.HomComplex
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.Sites.Equivalence
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
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
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
import Mathlib.Algebra.Homology.QuasiIso
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Homology.Functor

/-! # Definitions and normalized representatives for two-injective Hom

Source: Stacks Project, Tags 0A95 and 08J7; the internal-Hom paragraph of
blueprint/sec-six-functors/sk-thm-sf-package/cor-coef-verdier-weil-equivariance.proof.md;
the native signed model in WeilConjectures.WeilSheaf.DerivedHom
(blueprint: def-sf-ringed-two-injective-models).

The comparison data specify product projections, not global Hom groups. The native
normalization retains the row sign of bifunctorHomObj and its degree/source-index correction.
-/

@[expose] public noncomputable section

set_option genSizeOfSpec false
set_option genInjectivity false
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe b vb wb a va wa c v r d vd s u

open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures

attribute [local irreducible] homComplexFunctor homComplexπ derivedInternalHomOfUniverses
  coefficientHomResolutionIso

namespace CategoryTheory.RingedForgetTwoInjective

section Representatives

variable {B : Type b} [Category.{vb} B] [Abelian B] [HasDerivedCategory.{wb} B]

/-- The representative isomorphisms, including both variable squares and quasi-isomorphism
invariance. Source: Stacks 0A95 and 08J7
(blueprint: def-sf-ringed-two-injective-models). -/
structure Representatives
    (H : (CochainComplex B ℤ)ᵒᵖ × CochainComplex B ℤ ⥤ CochainComplex B ℤ)
    (DH : (DerivedCategory B)ᵒᵖ × DerivedCategory B ⥤ DerivedCategory B) where
  /-- An arbitrary source complex and any K-injective target compute the derived Hom. -/
  iso (K I : CochainComplex B ℤ) [I.IsKInjective] :
    DH.obj (op (DerivedCategory.Q.obj K), DerivedCategory.Q.obj I) ≅
      DerivedCategory.Q.obj (H.obj (op K, I))
  /-- These are simultaneous natural identifications, including source resolutions. -/
  naturality (K K' I I' : CochainComplex B ℤ) [I.IsKInjective] [I'.IsKInjective]
      (f : K' ⟶ K) (g : I ⟶ I') :
    DH.map (X := (op (DerivedCategory.Q.obj K), DerivedCategory.Q.obj I))
        (Y := (op (DerivedCategory.Q.obj K'), DerivedCategory.Q.obj I'))
        ((DerivedCategory.Q.map f).op, DerivedCategory.Q.map g) ≫
        (iso K' I').hom =
      (iso K I).hom ≫ DerivedCategory.Q.map (H.map (X := (op K, I)) (Y := (op K', I')) (f.op, g))
  /-- Both target replacements and source resolutions become invertible. -/
  inverts (K K' I I' : CochainComplex B ℤ) [I.IsKInjective] [I'.IsKInjective]
      (f : K' ⟶ K) (g : I ⟶ I') [QuasiIso f] [QuasiIso g] :
    IsIso (DerivedCategory.Q.map (H.map (X := (op K, I)) (Y := (op K', I')) (f.op, g)))

/-- The representative square for a derived comparison, with all localization factors
included. Source: Stacks 0A95 and 08J7
(blueprint: def-sf-ringed-two-injective-models). -/
def DerivedCompatibility
    {A : Type a} [Category.{va} A] [Abelian A] [HasDerivedCategory.{wa} A]
    (U : B ⥤ A) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (hU : U.PreservesKInjectiveComplexes)
    (HB : (CochainComplex B ℤ)ᵒᵖ × CochainComplex B ℤ ⥤ CochainComplex B ℤ)
    (HA : (CochainComplex A ℤ)ᵒᵖ × CochainComplex A ℤ ⥤ CochainComplex A ℤ)
    (DB : (DerivedCategory B)ᵒᵖ × DerivedCategory B ⥤ DerivedCategory B)
    (DA : (DerivedCategory A)ᵒᵖ × DerivedCategory A ⥤ DerivedCategory A)
    (ρB : Representatives HB DB) (ρA : Representatives HA DA)
    (chain : HB ⋙ U.mapHomologicalComplex (.up ℤ) ≅
      ((U.mapHomologicalComplex (.up ℤ)).op.prod (U.mapHomologicalComplex (.up ℤ))) ⋙ HA)
    (derived : DB ⋙ U.mapDerivedCategory ≅
      (U.mapDerivedCategory.op.prod U.mapDerivedCategory) ⋙ DA) : Prop :=
  letI := hU
  ∀ (K I : CochainComplex B ℤ) [K.IsKInjective] [I.IsKInjective],
    derived.hom.app (op (DerivedCategory.Q.obj K), DerivedCategory.Q.obj I) ≫
        DA.map (X := (op (U.mapDerivedCategory.obj (DerivedCategory.Q.obj K)),
            U.mapDerivedCategory.obj (DerivedCategory.Q.obj I)))
          (Y := (op (DerivedCategory.Q.obj ((U.mapHomologicalComplex (.up ℤ)).obj K)),
            DerivedCategory.Q.obj ((U.mapHomologicalComplex (.up ℤ)).obj I)))
          ((U.mapDerivedCategoryFactors.inv.app K).op,
            U.mapDerivedCategoryFactors.hom.app I) ≫
        (ρA.iso ((U.mapHomologicalComplex (.up ℤ)).obj K)
          ((U.mapHomologicalComplex (.up ℤ)).obj I)).hom =
      U.mapDerivedCategory.map (ρB.iso K I).hom ≫
        U.mapDerivedCategoryFactors.hom.app (HB.obj (op K, I)) ≫
        DerivedCategory.Q.map (chain.hom.app (op K, I))

end Representatives

section RingedRepresentatives

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})
  [HasDerivedCategory.{wb} (RingedTensorModules.{c, v, r} J R)]

/-- The actual augmentation used in the recorded Hom replacement.
Source: Stacks 079P and 0A95 (blueprint: def-sf-ringed-two-injective-models). -/
def augmentation : 𝟭 (CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ) ⟶
    coefficientHomResolution.{r, c, v} J R :=
  letI :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, r}
      J R).1
  CochainComplex.toKInjectiveResolution.{max c v r} _

/-- The representative maps are normalized by the actual localization factorization and
augmentation of the recorded internal Hom. Source: Stacks 0A95 and 08J7
(blueprint: def-sf-ringed-two-injective-models). -/
structure RingedRepresentatives extends Representatives
    (Functor.uncurry.obj (homComplexFunctor (R := R)))
    (derivedInternalHomOfUniverses.{c, v, r, wb} J R) where
  /-- This equality fixes the comparison, ruling out an arbitrary automorphism of RHom. -/
  normalization (K I : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
      [I.IsKInjective] :
    (iso K I).hom ≫ DerivedCategory.Q.map
        (((homComplexFunctor (R := R)).obj (op K)).map
          ((augmentation.{c, v, r} J R).app I)) =
      (coefficientHomResolutionIso.{r, c, v, wb} J R K I).hom

/-- All K-injective representative choices give the same, natural internal-Hom model.
Source: Stacks 0A95 and 08J7
(blueprint: def-sf-ringed-two-injective-models).
Proof: factor RHom through its fixed functorial K-injective replacement. For a K-injective
I the augmentation I → I(I) is a quasi-isomorphism between K-injectives, so the Hom complex
inverts it (lem-pur-rhom-well-defined). Invert this map after Q to obtain the normalized iso.
Naturality of the augmentation gives both squares. Source quasi-isomorphisms and target
quasi-isomorphisms between K-injectives are inverted by the same lemma. Derived arrows are
unique homotopy classes between K-injectives (lem-weil-pbc-kinjective-hom-derived), hence these
squares give independence, the cocycle identity, and naturality for all derived arrows.
In particular take a K-injective source J representing K and any K-injective I representing L;
transport along their specified derived identifications. Precomposition by K° → J gives
exactly the source-resolution arrow Q Hom(J,I) → Q Hom(K°,I), with its stated direction. -/
theorem ringedRepresentatives : Nonempty (RingedRepresentatives.{wb, c, v, r} J R) := by
  let : IsGrothendieckAbelian.{max c v r} (RingedTensorModules.{c, v, r} J R) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, r}
      J R).1
  let H := Functor.uncurry.obj (homComplexFunctor (R := R))
  let e : (DerivedCategory.Q.op.prod DerivedCategory.Q) ⋙
      derivedInternalHomOfUniverses.{c, v, r, wb} J R ≅
      (𝟭 _).prod (coefficientHomResolution.{r, c, v} J R) ⋙ H ⋙ DerivedCategory.Q := by
    unfold derivedInternalHomOfUniverses coefficientHomResolution
    exact Localization.fac _
      (derivedInternalHomOfUniverses_inverts.{c, v, r, wb} J R _
        (CochainComplex.toKInjectiveResolution.{max c v r} _)
        (fun I ↦ ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{max c v r}
          _ I).2, CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{max c v r}
            _ I⟩)) (DerivedCategory.Q.op.prod DerivedCategory.Q)
  let α : H ⋙ DerivedCategory.Q ⟶
      (DerivedCategory.Q.op.prod DerivedCategory.Q) ⋙
        derivedInternalHomOfUniverses.{c, v, r, wb} J R :=
    Functor.whiskerRight (NatTrans.prod (𝟙 (𝟭 _)) (augmentation.{c, v, r} J R))
      (H ⋙ DerivedCategory.Q) ≫ e.inv
  have hα (K I : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
      [I.IsKInjective] : IsIso (α.app (op K, I)) := by
    have : ((coefficientHomResolution.{r, c, v} J R).obj I).IsKInjective :=
      CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{max c v r} _ I
    have : QuasiIso ((augmentation.{c, v, r} J R).app I) :=
      (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{max c v r} _ I).2
    have hq := quasiIso_homComplex_mapOfUniverses.{c, v, r}
      (I' := I) (I := (coefficientHomResolution.{r, c, v} J R).obj I)
      ((augmentation.{c, v, r} J R).app I) (𝟙 K)
    have : IsIso (DerivedCategory.Q.map
        (((homComplexFunctor (R := R)).obj (op K)).map
          ((augmentation.{c, v, r} J R).app I))) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr (by simpa using hq)
    dsimp [α, H]
    infer_instance
  let ρ : RingedRepresentatives.{wb, c, v, r} J R :=
    { iso := fun K I ↦ (asIso (α.app (op K, I))).symm
      naturality := by
        intro K K' I I' _ _ f g
        apply (cancel_mono (α.app (op K', I'))).1
        simp only [Category.assoc, Iso.symm_hom, asIso_inv, IsIso.inv_hom_id,
          Category.comp_id]
        have hn := α.naturality
          (X := (op K, I)) (Y := (op K', I')) (f.op, g)
        dsimp only [Functor.comp_map, Functor.prod_map, Functor.op_map] at hn
        rw [hn, IsIso.inv_hom_id_assoc]
        rfl
      inverts := by
        intro K K' I I' _ _ f g _ _
        exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr
          (quasiIso_homComplex_mapOfUniverses.{c, v, r} g f)
      normalization := by
        intro K I _
        change inv (α.app (op K, I)) ≫ _ = _
        apply (cancel_epi (α.app (op K, I))).1
        simp only [IsIso.hom_inv_id_assoc]
        change _ = (_ ≫ e.inv.app (op K, I)) ≫
          (coefficientHomResolutionIso.{r, c, v, wb} J R K I).hom
        have he : (coefficientHomResolutionIso.{r, c, v, wb} J R K I).hom =
            e.hom.app (op K, I) := by
          unfold coefficientHomResolutionIso
          rfl
        rw [he]
        simp [H, Functor.uncurry] }
  exact ⟨ρ⟩

end RingedRepresentatives

section Forgetting

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})
  {D : Type d} [Category.{vd} D] (J' : GrothendieckTopology D)
  [HasSheafify J' AddCommGrpCat.{max d vd s}]
  [J'.WEqualsLocallyBijective AddCommGrpCat.{max d vd s}]
  (R' : Sheaf J' CommRingCat.{max d vd s})
  [HasDerivedCategory.{wb} (RingedTensorModules.{c, v, r} J R)]
  [HasDerivedCategory.{wa} (RingedTensorModules.{d, vd, s} J' R')]
  (U : RingedTensorModules.{c, v, r} J R ⥤ RingedTensorModules.{d, vd, s} J' R')
  [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  [∀ A : Type (max c v r), PreservesLimitsOfShape (Discrete A) U]
  [U.PreservesKInjectiveComplexes]
  (h : Functor.uncurry.obj (SheafOfModules.homFunctor (R := R)) ⋙ U ≅
    (U.op.prod U) ⋙ Functor.uncurry.obj (SheafOfModules.homFunctor (R := R')))

/-- The specified sheaf-Hom comparison on product-total complexes and on derived objects.
Source: Stacks 0A95 and 08J7, componentwise forgetting calculation in the blueprint
(blueprint: def-sf-ringed-two-injective-models). -/
structure Comparison where
  /-- The normalized representative model on the source site. -/
  source : RingedRepresentatives.{wb, c, v, r} J R
  /-- The normalized representative model on the target site. -/
  target : RingedRepresentatives.{wa, d, vd, s} J' R'
  /-- A simultaneous chain isomorphism, natural contravariantly and covariantly. -/
  chain : Functor.uncurry.obj (homComplexFunctor (R := R)) ⋙
      U.mapHomologicalComplex (.up ℤ) ≅
    ((U.mapHomologicalComplex (.up ℤ)).op.prod (U.mapHomologicalComplex (.up ℤ))) ⋙
      Functor.uncurry.obj (homComplexFunctor (R := R'))
  /-- Its projection is U(π_p) followed by precisely the specified Hom comparison. -/
  projection (K I : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
      (n p q : ℤ) (hpq : p + n = q) :
    (chain.hom.app (op K, I)).f n ≫
        homComplexπ (R := R') ((U.mapHomologicalComplex (.up ℤ)).obj K)
          ((U.mapHomologicalComplex (.up ℤ)).obj I) n p q hpq =
      U.map (homComplexπ (R := R) K I n p q hpq) ≫
        h.hom.app (op (K.X p), I.X q)
  /-- The required natural isomorphism χ on the two derived variables. -/
  derived : derivedInternalHomOfUniverses.{c, v, r, wb} J R ⋙ U.mapDerivedCategory ≅
    (U.mapDerivedCategory.op.prod U.mapDerivedCategory) ⋙
      derivedInternalHomOfUniverses.{d, vd, s, wa} J' R'
  /-- χ is represented by chain on every two-K-injective model. -/
  representative (K I : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
      [K.IsKInjective] [I.IsKInjective] :
    derived.hom.app (op (DerivedCategory.Q.obj K), DerivedCategory.Q.obj I) ≫
        (derivedInternalHomOfUniverses.{d, vd, s, wa} J' R').map
          (X := (op (U.mapDerivedCategory.obj (DerivedCategory.Q.obj K)),
            U.mapDerivedCategory.obj (DerivedCategory.Q.obj I)))
          (Y := (op (DerivedCategory.Q.obj ((U.mapHomologicalComplex (.up ℤ)).obj K)),
            DerivedCategory.Q.obj ((U.mapHomologicalComplex (.up ℤ)).obj I)))
          ((U.mapDerivedCategoryFactors.inv.app K).op,
            U.mapDerivedCategoryFactors.hom.app I) ≫
        (target.iso ((U.mapHomologicalComplex (.up ℤ)).obj K)
          ((U.mapHomologicalComplex (.up ℤ)).obj I)).hom =
      U.mapDerivedCategory.map (source.iso K I).hom ≫
        U.mapDerivedCategoryFactors.hom.app (homComplex (R := R) K I) ≫
        DerivedCategory.Q.map (chain.hom.app (op K, I))

end Forgetting
section StandardModel

variable {B : Type b} [Category.{vb} B] [Preadditive B]

/-- A product-total internal Hom with the standard cohomological differential. This is
representative data, not a new choice of internal sheaf Hom.
Source: Stacks 0A8X (blueprint: def-sf-ringed-two-injective-models). -/
structure StandardModel (H : Bᵒᵖ ⥤ B ⥤ B) where
  /-- The complex-valued bifunctor. -/
  complex : (CochainComplex B ℤ)ᵒᵖ × CochainComplex B ℤ ⥤ CochainComplex B ℤ
  /-- The actual internal-Hom product factors. -/
  π (K I : CochainComplex B ℤ) (n p q : ℤ) (hpq : p + n = q) :
    (complex.obj (op K, I)).X n ⟶ (H.obj (op (K.X p))).obj (I.X q)
  /-- These factors are a product in the module category, including all integer indices. -/
  product (K I : CochainComplex B ℤ) (n : ℤ) :
    IsLimit (Fan.mk ((complex.obj (op K, I)).X n) (fun p ↦ π K I n p (p + n) rfl))
  /-- The differential is d_I f - (-1)^n f d_K. -/
  differential (K I : CochainComplex B ℤ) (n m p q q' p' : ℤ)
      (hnm : n + 1 = m) (hpq : p + m = q) (hq' : p + n = q') (hp' : p' + n = q) :
    (complex.obj (op K, I)).d n m ≫ π K I m p q hpq =
      π K I n p q' hq' ≫ (H.obj (op (K.X p))).map (I.d q' q) -
        n.negOnePow • (π K I n p' q hp' ≫ (H.map (K.d p p').op).app (I.X q))
  /-- Both functor variables act by ordinary pre- and post-composition. -/
  map_projection (K K' I I' : CochainComplex B ℤ) (f : K' ⟶ K) (g : I ⟶ I')
      (n p q : ℤ) (hpq : p + n = q) :
    (complex.map (X := (op K, I)) (Y := (op K', I')) (f.op, g)).f n ≫
        π K' I' n p q hpq =
      π K I n p q hpq ≫ (H.map (f.f p).op).app (I.X q) ≫
        (H.obj (op (K'.X p))).map (g.f q)

end StandardModel
end CategoryTheory.RingedForgetTwoInjective

namespace AlgebraicGeometry.ProEtaleWeilSheaf

open CategoryTheory.RingedForgetTwoInjective

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ}
  [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- The existing internal Hom of the underlying continuous-coefficient modules, as a
bifunctor. The morphism laws are the existing laws of Mod.ihomMap.
Source: native Adic/Hom.lean (blueprint: def-sf-ringed-two-injective-models). -/
def underlyingHomBifunctor :
    (ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)ᵒᵖ ⥤
      ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber ⥤
        ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber where
  obj M := ProEtale.AdicSheaf.ihom M.unop
  map f := Mod.ihomMap f.unop
  map_id M := Mod.ihomMap_id M.unop
  map_comp f g := Mod.ihomMap_comp g.unop f.unop

/-- The existing exact orbit-induction criterion, with the countable index universe
specified explicitly. This is the existing preservation proof, not an extra hypothesis.
Source: IsoAlgebra.preservesKInjectiveComplexes_forget and the twisted action site
(blueprint: def-sf-ringed-two-injective-models). -/
abbrev forgetKInjective : (Endofunctor.IsoAlgebra.forget
    (WeilSheaf.frobeniusPullback k₀ l X)).PreservesKInjectiveComplexes :=
  let A := ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
  letI : HasColimitsOfSize.{u + 1, u + 1} A := inferInstance
  letI : HasColimitsOfSize.{0, 0} A := hasColimitsOfSizeShrink.{0, 0, u + 1, u + 1} A
  letI : HasCoproducts.{u + 1} A := fun J ↦
    HasColimitsOfSize.has_colimits_of_shape (Discrete J)
  letI : HasCoproducts.{0} A := fun J ↦
    HasColimitsOfSize.has_colimits_of_shape (Discrete J)
  letI : AB4OfSize.{u + 1} A := inferInstance
  letI : AB4OfSize.{0} A := AB4OfSize_shrink.{0, u + 1} A
  letI : HasExactColimitsOfShape (Discrete ℤ) A := inferInstance
  Endofunctor.IsoAlgebra.preservesKInjectiveComplexes_forget _

/-- The full native specialization, keeping the equivariant product-total complex and its
specified row-sign normalization. All projections and sign maps are morphisms of Weil
sheaves, hence preserve the contragredient action, not merely the underlying modules.
Source: native DerivedHom.lean, BifunctorHomComplex.lean and TateTwistCohomology.lean;
Stacks 0A95 and 08J7 (blueprint: def-sf-ringed-two-injective-models). -/
structure TwoInjectiveHomModel where
  /-- The finite-span native coefficient interpretation is the finite-subextension one,
  locally on every object, so the pointwise rings and precomposition restrictions agree. -/
  coefficients (T : Type u) [TopologicalSpace T] (f : C(T, PadicAlgCl l)) :
    f ∈ PadicAlgCl.locallyFiniteFunctions l T ↔
      ∀ x : T, ∃ N ∈ nhds x, ∃ E : PadicAlgCl.FiniteIntermediateField l,
        ∀ y ∈ N, f y ∈ E.val
  /-- The standard-sign product-total complex in the actual native fixed-pair category. -/
  source : StandardModel (ihomBifunctor k₀ l X)
  /-- The standard-sign complex over the underlying continuous coefficient sheaf. -/
  target : StandardModel (underlyingHomBifunctor (k₀ := k₀) (l := l) (X := X))
  /-- The native-to-standard sign conversion is an isomorphism of equivariant complexes. -/
  sign (K I : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) :
    CochainComplex.bifunctorHomObj (ihomBifunctor k₀ l X) K I ≅
      source.complex.obj (op K, I)
  /-- Its (n,p) component is exactly (-1)^(np). -/
  sign_projection (K I : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
      (n p q : ℤ) (hpq : p + n = q) :
    (sign K I).hom.f n ≫ source.π K I n p q hpq =
      (n * p).negOnePow • CochainComplex.bifunctorHomπ (ihomBifunctor k₀ l X) K I n p q hpq
  /-- Sign conversion is natural in both complex variables. -/
  sign_naturality (K K' I I' : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
      (f : K' ⟶ K) (g : I ⟶ I') :
    CochainComplex.bifunctorHomMapLeft (H := ihomBifunctor k₀ l X) (Y := I) f ≫
        CochainComplex.bifunctorHomMapRight (H := ihomBifunctor k₀ l X) (K := K') g ≫
        (sign K' I').hom =
      (sign K I).hom ≫ source.complex.map (X := (op K, I)) (Y := (op K', I')) (f.op, g)
  /-- RHom as a bifunctor, with the native functor recovered below, not an alternative RHom. -/
  hom : (DerivedCategory (ProEtaleWeilSheaf k₀ l X))ᵒᵖ ×
    DerivedCategory (ProEtaleWeilSheaf k₀ l X) ⥤ DerivedCategory (ProEtaleWeilSheaf k₀ l X)
  /-- Both variables and all K-injective representatives descend naturally. -/
  representatives : Representatives source.complex hom
  /-- The underlying module derived internal Hom on this same coefficient sheaf. -/
  underlyingHom :
    (DerivedCategory (ProEtale.AdicSheaf l
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber))ᵒᵖ ×
      DerivedCategory (ProEtale.AdicSheaf l
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ⥤
          DerivedCategory (ProEtale.AdicSheaf l
            (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
  /-- Its computation is on the same two-injective product-total model. -/
  underlyingRepresentatives : Representatives target.complex underlyingHom
  /-- The specialization is the existing native derivedHom, natural in the source. -/
  native (L : DerivedCategory (ProEtaleWeilSheaf k₀ l X)) :
    Prod.sectL (DerivedCategory (ProEtaleWeilSheaf k₀ l X))ᵒᵖ L ⋙ hom ≅ derivedHom k₀ l X L
  /-- This identification is fixed by the native source comparison and its chosen target. -/
  native_normalization (L : DerivedCategory (ProEtaleWeilSheaf k₀ l X))
      (K : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) [K.IsKInjective] :
    (native L).hom.app (op (DerivedCategory.Q.obj K)) ≫
        (DerivedCategory.bifunctorRHomOfComplexObjIso (ihomBifunctor k₀ l X)
          (DerivedCategory.kInjectiveRep L) K).hom ≫
        DerivedCategory.Q.map (sign K (DerivedCategory.kInjectiveRep L)).hom =
      hom.map (X := (op (DerivedCategory.Q.obj K), L))
          (Y := (op (DerivedCategory.Q.obj K),
            DerivedCategory.Q.obj (DerivedCategory.kInjectiveRep L)))
          (𝟙 _, (DerivedCategory.kInjectiveRepIso L).hom) ≫
        (representatives.iso K (DerivedCategory.kInjectiveRep L)).hom
  /-- Forgetting acts on all product projections through the actual sheaf-Hom comparison. -/
  chain : source.complex ⋙
      (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex
        (.up ℤ) ≅
    (((Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex
        (.up ℤ)).op.prod
      ((Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex
        (.up ℤ))) ⋙ target.complex
  /-- The product projection equation uses the native identity on underlying internal Homs. -/
  chain_projection (K I : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
      (n p q : ℤ) (hpq : p + n = q) :
    (chain.hom.app (op K, I)).f n ≫
        target.π
          (((Endofunctor.IsoAlgebra.forget _).mapHomologicalComplex (.up ℤ)).obj K)
          (((Endofunctor.IsoAlgebra.forget _).mapHomologicalComplex (.up ℤ)).obj I) n p q hpq =
      (Endofunctor.IsoAlgebra.forget _).map (source.π K I n p q hpq) ≫
        (ihomFunctorCompForgetIso k₀ l X (K.X p)).hom.app (I.X q)
  /-- The natural derived comparison for the actual underlying-module functor. -/
  derived : hom ⋙ (Endofunctor.IsoAlgebra.forget
      (WeilSheaf.frobeniusPullback k₀ l X)).mapDerivedCategory ≅
    ((Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).mapDerivedCategory.op.prod
      (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).mapDerivedCategory) ⋙
        underlyingHom
  /-- χ is the localization of the specified projectionwise comparison, for every pair
  of K-injectives. Thus naturality also controls replacement and inversion squares. -/
  derived_representative : DerivedCompatibility
    (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X))
    (forgetKInjective (k₀ := k₀) (l := l) (X := X))
    source.complex target.complex hom underlyingHom representatives underlyingRepresentatives
    chain derived

end AlgebraicGeometry.ProEtaleWeilSheaf
