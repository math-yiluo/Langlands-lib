/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.FiniteDualityLocallyClosedComparison
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.FixedComparisonDirectImageMate
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.AlgebraicGeometry.ImmersionProjectionComparison.ImmersionProjectionSiteComparison
public import WeilConjectures.AlgebraicGeometry.SixFunctors.EvaluationHomSiteComparison
public import WeilConjectures.AlgebraicGeometry.Etale.Closed.EtaleClosedAmbientAdjoint
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicClosedAmbient
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZeroExact
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.Algebra.Homology.Site.SiteDerivedTensorDescent
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
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
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
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
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.K.KInjectiveTotalDerived
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleGenericStratumMate
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.ConstructibleSheaf.Defs
/-! # Canonical data for the normalized stratum Hom comparison

Source: Weil blueprint, latest, sec-smooth-purity/sk-lem-sp-tower,
lem-weil-finite-duality-site-comparison.proof.md, second paragraph
(blueprint: def-sf-stratum-hom-comparison-data).

The two natural isomorphisms are specified by their inverse evaluation transposes.
The ordinary direct-image comparison below is literally the recorded bounded-below
mate, transported into the unbounded category by the canonical compatibility maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 2048
universe u u₁ v₁
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open scoped CategoryTheory.Functor MonoidalCategory

attribute [local instance high] GrothendieckTopology.W.monoidal
attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

namespace AlgebraicGeometry.StratumHomComparisonMate

/-- The two-variable internal-Hom comparison type.
Source: the stratum tensor-Hom adjunction in the finite-duality comparison proof
(blueprint: def-sf-stratum-hom-comparison-data). -/
def stratumHomIsoType
    {C D : Type*} [Category C] [Category D]
    (HS : Dᵒᵖ ⥤ D ⥤ D) (HX : Cᵒᵖ ⥤ C ⥤ C)
    (F : D ⥤ C) (G : C ⥤ D) (R : D ⥤ C) :=
  F.op.prod (𝟭 C) ⋙ Functor.uncurry.obj HX ≅
    (𝟭 Dᵒᵖ).prod G ⋙ Functor.uncurry.obj HS ⋙ R

/-- Evaluation normalization for a tensor-Hom comparison.
Source: the inverse evaluation formula in the finite-duality comparison proof
(blueprint: def-sf-stratum-hom-comparison-data). -/
@[irreducible]
def tensorHomNormalization
    {C D : Type*} [Category C] [Category D]
    (TS : D ⥤ D ⥤ D) (HS : Dᵒᵖ ⥤ D ⥤ D)
    (TX : C ⥤ C ⥤ C) (HX : Cᵒᵖ ⥤ C ⥤ C)
    (F : D ⥤ C) (G : C ⥤ D) (L : C ⥤ D) (R : D ⥤ C)
    (a : L ⊣ R) (b : F ⊣ G)
    (evX : ∀ P M : C, (TX.obj ((HX.obj (op P)).obj M)).obj P ⟶ M)
    (evS : ∀ P M : D, (TS.obj ((HS.obj (op P)).obj M)).obj P ⟶ M)
    (proj : ∀ (T : C) (P : D), (TX.obj T).obj (F.obj P) ⟶
      F.obj ((TS.obj (L.obj T)).obj P))
    (θ : stratumHomIsoType HS HX F G R) : Prop :=
      ∀ P M, (TX.map (θ.inv.app (op P, M))).app (F.obj P) ≫ evX (F.obj P) M =
        proj (R.obj ((HS.obj (op P)).obj (G.obj M))) P ≫
          F.map ((TS.map (a.counit.app ((HS.obj (op P)).obj (G.obj M)))).app P) ≫
          F.map (evS P (G.obj M)) ≫ b.counit.app M

namespace Etale

/-- The existing ordinary derived category, in the fixed-scalar presentation.
Source: blueprint finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-stratum-hom-comparison-mate). -/
abbrev D (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :=
  DerivedCategory (Sheaf (T.smallEtaleTopology) (ModuleCat.{u + 1} A))

/-- The existing K-injective internal Hom, with its contravariant first argument.
Source: blueprint finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-stratum-hom-comparison-mate). -/
abbrev hom (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (P B : D A T) :=
  ((AlgebraicGeometry.Etale.derivedHom (ModuleCat.{u + 1} A) T).obj (op P)).obj B

/-- The existing K-flat tensor, with the ambient factor written first.
Source: blueprint finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-stratum-hom-comparison-mate). -/
abbrev tensor (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (P B : D A T) :=
  ((AlgebraicGeometry.Etale.derivedTensor (ModuleCat.{u + 1} A) T).obj P).obj B

/-- Right-ordered evaluation, using the canonical signed tensor symmetry.
Source: blueprint finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-stratum-hom-comparison-mate). -/
def evaluation (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (P B : D A T) : tensor A T (hom A T P B) P ⟶ B :=
  ((ImmersionProjectionComparison.Etale.symmetry A T).hom.app (hom A T P B)).app P ≫
    (AlgebraicGeometry.Etale.derivedTensorHomAdjunction
      (ModuleCat.{u + 1} A) P).counit.app B

/-- Canonical identification of derived closed/open extension with exact termwise extension.
Source: blueprint finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-stratum-hom-comparison-mate). -/
def extensionIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V X : Scheme.{u}} [IsNoetherian X] (c : S ⟶ V) (v : V ⟶ X)
    [IsClosedImmersion c] [IsOpenImmersion v] :
    AlgebraicGeometry.ProEtale.locallyClosedEtaleExtension A c v ≅
      ImmersionProjectionComparison.Etale.extension A c v :=
  haveI : IsLocallyNoetherian V := isLocallyNoetherian_of_isOpenImmersion v
  haveI : CompactSpace V :=
    ⟨v.isOpenEmbedding.isInducing.isCompact_iff.2
      (TopologicalSpace.NoetherianSpace.isCompact _)⟩
  Functor.isoWhiskerRight
    (AlgebraicGeometry.Etale.lowerStar (ModuleCat.{u + 1} A) c
      ).rightDerivedFunctorIsoMapDerivedCategory
    (AlgebraicGeometry.Etale.openImmersionLowerShriek
      (ModuleCat.{u + 1} A) v).mapDerivedCategory

/-- Ordinary inverse/direct-image adjunction in the factorized restriction coordinates.
Source: blueprint finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-stratum-hom-comparison-mate). -/
@[irreducible]
def ordinaryAdjunction (A : Type (u + 1)) [CommRing A]
    {S V X : Scheme.{u}} (c : S ⟶ V) (v : V ⟶ X) :
    ImmersionProjectionComparison.Etale.pull A v ⋙
        ImmersionProjectionComparison.Etale.pull A c ⊣
      (AlgebraicGeometry.Etale.lowerStar (ModuleCat.{u + 1} A) (c ≫ v)
        ).rightDerivedFunctor :=
  (AlgebraicGeometry.Etale.derivedUpperStarLowerStarAdjunction
    (ModuleCat.{u + 1} A) (c ≫ v)).ofNatIsoLeft
      (AlgebraicGeometry.Etale.leftDerivedUpperStarComp
        (ModuleCat.{u + 1} A) c v ≪≫
        Functor.isoWhiskerRight
          (AlgebraicGeometry.Etale.leftDerivedUpperStarIsoMapDerivedCategory
            (ModuleCat.{u + 1} A) v) _ ≪≫
        Functor.isoWhiskerLeft _
          (AlgebraicGeometry.Etale.leftDerivedUpperStarIsoMapDerivedCategory
            (ModuleCat.{u + 1} A) c))

/-- The projection arrow of the dependency, transported to the ambient derived extension.
Source: blueprint finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-stratum-hom-comparison-mate). -/
def projection (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V X : Scheme.{u}} [IsNoetherian X] (c : S ⟶ V) (v : V ⟶ X)
    [IsClosedImmersion c] [IsOpenImmersion v] (T : D A X) (P : D A S) :
    tensor A X T
        ((AlgebraicGeometry.ProEtale.locallyClosedEtaleExtension A c v).obj P) ⟶
      (AlgebraicGeometry.ProEtale.locallyClosedEtaleExtension A c v).obj
        (tensor A S ((ImmersionProjectionComparison.Etale.pull A c).obj
          ((ImmersionProjectionComparison.Etale.pull A v).obj T)) P) :=
  ((AlgebraicGeometry.Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj T).map
      ((extensionIso A c v).hom.app P) ≫
    ImmersionProjectionComparison.Etale.projection A c v T P ≫
    (extensionIso A c v).inv.app
      (tensor A S ((ImmersionProjectionComparison.Etale.pull A c).obj
        ((ImmersionProjectionComparison.Etale.pull A v).obj T)) P)

/-- The type of natural stratum isomorphisms for the specified ambient right adjoint.
Source: blueprint finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-stratum-hom-comparison-mate). -/
abbrev HomIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V X : Scheme.{u}} (c : S ⟶ V) (v : V ⟶ X) [IsOpenImmersion v]
    (a : AlgebraicGeometry.ProEtale.LocallyClosedComparisonAdjoints A c) :=
  stratumHomIsoType
    (AlgebraicGeometry.Etale.derivedHom (ModuleCat.{u + 1} A) S)
    (AlgebraicGeometry.Etale.derivedHom (ModuleCat.{u + 1} A) X)
    (AlgebraicGeometry.ProEtale.locallyClosedEtaleExtension A c v) (a.etaleRight v)
    (AlgebraicGeometry.Etale.lowerStar (ModuleCat.{u + 1} A) (c ≫ v)).rightDerivedFunctor

/-- The displayed inverse-transpose normalization, for all two-variable inputs.
Source: blueprint finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-stratum-hom-comparison-mate). -/
def Normalized (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V X : Scheme.{u}} [IsNoetherian X] (c : S ⟶ V) (v : V ⟶ X)
    [IsClosedImmersion c] [IsOpenImmersion v]
    (a : AlgebraicGeometry.ProEtale.LocallyClosedComparisonAdjoints A c)
    (χ : HomIso A c v a) : Prop :=
  tensorHomNormalization
    (AlgebraicGeometry.Etale.derivedTensor (ModuleCat.{u + 1} A) S)
    (AlgebraicGeometry.Etale.derivedHom (ModuleCat.{u + 1} A) S)
    (AlgebraicGeometry.Etale.derivedTensor (ModuleCat.{u + 1} A) X)
    (AlgebraicGeometry.Etale.derivedHom (ModuleCat.{u + 1} A) X)
    (AlgebraicGeometry.ProEtale.locallyClosedEtaleExtension A c v) (a.etaleRight v)
    (ImmersionProjectionComparison.Etale.pull A v ⋙
      ImmersionProjectionComparison.Etale.pull A c)
    (AlgebraicGeometry.Etale.lowerStar (ModuleCat.{u + 1} A) (c ≫ v)).rightDerivedFunctor
    (ordinaryAdjunction A c v) (a.etalePasted v)
    (evaluation A X) (evaluation A S) (projection A c v) χ

end Etale

namespace ProEtale

/-- The existing ordinary derived category, in the fixed-scalar presentation.
Source: blueprint finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-stratum-hom-comparison-mate). -/
abbrev D (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :=
  DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))

/-- The existing K-injective internal Hom, with its contravariant first argument.
Source: blueprint finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-stratum-hom-comparison-mate). -/
abbrev hom (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (P B : D A T) :=
  ((AlgebraicGeometry.ProEtale.derivedHom (ModuleCat.{u + 1} A) T).obj (op P)).obj B

/-- The existing K-flat tensor, with the ambient factor written first.
Source: blueprint finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-stratum-hom-comparison-mate). -/
abbrev tensor (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (P B : D A T) :=
  ((AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) T).obj P).obj B

/-- Right-ordered evaluation, using the canonical signed tensor symmetry.
Source: blueprint finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-stratum-hom-comparison-mate). -/
def evaluation (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (P B : D A T) : tensor A T (hom A T P B) P ⟶ B :=
  ((ImmersionProjectionComparison.ProEtale.symmetry A T).hom.app (hom A T P B)).app P ≫
    (AlgebraicGeometry.ProEtale.derivedTensorHomAdjunction
      (ModuleCat.{u + 1} A) P).counit.app B

/-- Canonical identification of derived closed/open extension with exact termwise extension.
Source: blueprint finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-stratum-hom-comparison-mate). -/
def extensionIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V X : Scheme.{u}} [IsNoetherian X] (c : S ⟶ V) (v : V ⟶ X)
    [IsClosedImmersion c] [IsOpenImmersion v] :
    AlgebraicGeometry.ProEtale.locallyClosedProEtaleExtension A c v ≅
      ImmersionProjectionComparison.ProEtale.extension A c v :=
  haveI : IsLocallyNoetherian V := isLocallyNoetherian_of_isOpenImmersion v
  haveI : CompactSpace V :=
    ⟨v.isOpenEmbedding.isInducing.isCompact_iff.2
      (TopologicalSpace.NoetherianSpace.isCompact _)⟩
  Functor.isoWhiskerRight
    (AlgebraicGeometry.ProEtale.lowerStar (ModuleCat.{u + 1} A) c
      ).rightDerivedFunctorIsoMapDerivedCategory
    (AlgebraicGeometry.ProEtale.openImmersionLowerShriek
      (ModuleCat.{u + 1} A) v).mapDerivedCategory

/-- Ordinary inverse/direct-image adjunction in the factorized restriction coordinates.
Source: blueprint finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-stratum-hom-comparison-mate). -/
@[irreducible]
def ordinaryAdjunction (A : Type (u + 1)) [CommRing A]
    {S V X : Scheme.{u}} (c : S ⟶ V) (v : V ⟶ X) :
    ImmersionProjectionComparison.ProEtale.pull A v ⋙
        ImmersionProjectionComparison.ProEtale.pull A c ⊣
      (AlgebraicGeometry.ProEtale.lowerStar (ModuleCat.{u + 1} A) (c ≫ v)
        ).rightDerivedFunctor :=
  (AlgebraicGeometry.ProEtale.derivedUpperStarLowerStarAdjunction
    (ModuleCat.{u + 1} A) (c ≫ v)).ofNatIsoLeft
      (AlgebraicGeometry.ProEtale.leftDerivedUpperStarComp
        (ModuleCat.{u + 1} A) c v ≪≫
        Functor.isoWhiskerRight
          (AlgebraicGeometry.ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
            (ModuleCat.{u + 1} A) v) _ ≪≫
        Functor.isoWhiskerLeft _
          (AlgebraicGeometry.ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
            (ModuleCat.{u + 1} A) c))

/-- The projection arrow of the dependency, transported to the ambient derived extension.
Source: blueprint finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-stratum-hom-comparison-mate). -/
def projection (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V X : Scheme.{u}} [IsNoetherian X] (c : S ⟶ V) (v : V ⟶ X)
    [IsClosedImmersion c] [IsOpenImmersion v] (T : D A X) (P : D A S) :
    tensor A X T
        ((AlgebraicGeometry.ProEtale.locallyClosedProEtaleExtension A c v).obj P) ⟶
      (AlgebraicGeometry.ProEtale.locallyClosedProEtaleExtension A c v).obj
        (tensor A S ((ImmersionProjectionComparison.ProEtale.pull A c).obj
          ((ImmersionProjectionComparison.ProEtale.pull A v).obj T)) P) :=
  ((AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) X).obj T).map
      ((extensionIso A c v).hom.app P) ≫
    ImmersionProjectionComparison.ProEtale.projection A c v T P ≫
    (extensionIso A c v).inv.app
      (tensor A S ((ImmersionProjectionComparison.ProEtale.pull A c).obj
        ((ImmersionProjectionComparison.ProEtale.pull A v).obj T)) P)

/-- The type of natural stratum isomorphisms for the specified ambient right adjoint.
Source: blueprint finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-stratum-hom-comparison-mate). -/
abbrev HomIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V X : Scheme.{u}} (c : S ⟶ V) (v : V ⟶ X) [IsOpenImmersion v]
    (a : AlgebraicGeometry.ProEtale.LocallyClosedComparisonAdjoints A c) :=
  stratumHomIsoType
    (AlgebraicGeometry.ProEtale.derivedHom (ModuleCat.{u + 1} A) S)
    (AlgebraicGeometry.ProEtale.derivedHom (ModuleCat.{u + 1} A) X)
    (AlgebraicGeometry.ProEtale.locallyClosedProEtaleExtension A c v) (a.proetaleRight v)
    (AlgebraicGeometry.ProEtale.lowerStar (ModuleCat.{u + 1} A) (c ≫ v)).rightDerivedFunctor

/-- The displayed inverse-transpose normalization, for all two-variable inputs.
Source: blueprint finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-stratum-hom-comparison-mate). -/
def Normalized (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V X : Scheme.{u}} [IsNoetherian X] (c : S ⟶ V) (v : V ⟶ X)
    [IsClosedImmersion c] [IsOpenImmersion v]
    (a : AlgebraicGeometry.ProEtale.LocallyClosedComparisonAdjoints A c)
    (χ : HomIso A c v a) : Prop :=
  tensorHomNormalization
    (AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) S)
    (AlgebraicGeometry.ProEtale.derivedHom (ModuleCat.{u + 1} A) S)
    (AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) X)
    (AlgebraicGeometry.ProEtale.derivedHom (ModuleCat.{u + 1} A) X)
    (AlgebraicGeometry.ProEtale.locallyClosedProEtaleExtension A c v) (a.proetaleRight v)
    (ImmersionProjectionComparison.ProEtale.pull A v ⋙
      ImmersionProjectionComparison.ProEtale.pull A c)
    (AlgebraicGeometry.ProEtale.lowerStar (ModuleCat.{u + 1} A) (c ≫ v)).rightDerivedFunctor
    (ordinaryAdjunction A c v) (a.proetalePasted v)
    (evaluation A X) (evaluation A S) (projection A c v) χ

end ProEtale

/-- The specified D+ direct-image mate in the ordinary unbounded categories.
Source: blueprint finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-stratum-hom-comparison-mate). -/
def directImageMate (A : Type (u + 1)) [CommRing A]
    {S X : Scheme.{u}} (s : S ⟶ X)
    (K : DerivedCategory.Plus (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (ImmersionProjectionComparison.comparison A X).obj
        ((AlgebraicGeometry.Etale.lowerStar (ModuleCat.{u + 1} A) s
          ).rightDerivedFunctor.obj K.obj) ⟶
      (AlgebraicGeometry.ProEtale.lowerStar (ModuleCat.{u + 1} A) s
        ).rightDerivedFunctor.obj ((ImmersionProjectionComparison.comparison A S).obj K.obj) :=
  (ImmersionProjectionComparison.comparison A X).map
      ((AlgebraicGeometry.Etale.lowerStar (ModuleCat.{u + 1} A) s
        ).rightDerivedFunctorPlusCompatibility.inv.app K) ≫
    (AlgebraicGeometry.ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X
      ).mapDerivedCategoryPlusCompatibility.inv.app
        ((AlgebraicGeometry.Etale.lowerStar (ModuleCat.{u + 1} A) s
          ).rightDerivedFunctorPlus.obj K) ≫
    DerivedCategory.Plus.ι.map
      ((AlgebraicGeometry.ProEtale.fixedComparisonDirectImageMatePlus A s).app K) ≫
    (AlgebraicGeometry.ProEtale.lowerStar (ModuleCat.{u + 1} A) s
      ).rightDerivedFunctorPlusCompatibility.hom.app
        ((AlgebraicGeometry.ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) S
          ).mapDerivedCategoryPlus.obj K) ≫
    (AlgebraicGeometry.ProEtale.lowerStar (ModuleCat.{u + 1} A) s).rightDerivedFunctor.map
      ((AlgebraicGeometry.ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) S
        ).mapDerivedCategoryPlusCompatibility.hom.app K)

/-- Delta with exactly the canonical closed-mate and open-unit normalization.
Source: blueprint finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-stratum-hom-comparison-mate). -/
def extensionComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V X : Scheme.{u}} [IsNoetherian X] (c : S ⟶ V) (v : V ⟶ X)
    [IsClosedImmersion c] [IsOpenImmersion v] (P : Etale.D A S) :
    (ImmersionProjectionComparison.comparison A X).obj
        ((AlgebraicGeometry.ProEtale.locallyClosedEtaleExtension A c v).obj P) ≅
      (AlgebraicGeometry.ProEtale.locallyClosedProEtaleExtension A c v).obj
        ((ImmersionProjectionComparison.comparison A S).obj P) :=
  (ImmersionProjectionComparison.comparison A X).mapIso
      ((Etale.extensionIso A c v).app P) ≪≫
    ImmersionProjectionComparison.extensionComparison A c v P ≪≫
    ((ProEtale.extensionIso A c v).app
      ((ImmersionProjectionComparison.comparison A S).obj P)).symm

/-- The contravariant Hom identification induced by the inverse of Delta.
Source: blueprint finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-stratum-hom-comparison-mate). -/
def homChange (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V X : Scheme.{u}} [IsNoetherian X] (c : S ⟶ V) (v : V ⟶ X)
    [IsClosedImmersion c] [IsOpenImmersion v] (P : Etale.D A S) (B : Etale.D A X) :
    ProEtale.hom A X
        ((ImmersionProjectionComparison.comparison A X).obj
          ((AlgebraicGeometry.ProEtale.locallyClosedEtaleExtension A c v).obj P))
        ((ImmersionProjectionComparison.comparison A X).obj B) ⟶
      ProEtale.hom A X
        ((AlgebraicGeometry.ProEtale.locallyClosedProEtaleExtension A c v).obj
          ((ImmersionProjectionComparison.comparison A S).obj P))
        ((ImmersionProjectionComparison.comparison A X).obj B) :=
  ((AlgebraicGeometry.ProEtale.derivedHom (ModuleCat.{u + 1} A) X).map
    (extensionComparison A c v P).inv.op).app
      ((ImmersionProjectionComparison.comparison A X).obj B)

/-- The stratum arrow H(1,gamma) after the evaluation-defined comparison beta.
Source: blueprint finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-stratum-hom-comparison-mate). -/
def stratumMap (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V X : Scheme.{u}} [IsNoetherian X] (c : S ⟶ V) (v : V ⟶ X)
    [IsClosedImmersion c] [IsOpenImmersion v] [QuasiCompact (c ≫ v)]
    (z : AlgebraicGeometry.ProEtale.LocallyClosedExceptionalComparison A c v)
    (P : Etale.D A S) (M : AlgebraicGeometry.Etale.BoundedConstructibleDerivedCategory A X) :
    (ImmersionProjectionComparison.comparison A S).obj
        (Etale.hom A S P ((z.adjoints.etaleRight v).obj M.obj)) ⟶
      ProEtale.hom A S ((ImmersionProjectionComparison.comparison A S).obj P)
        ((z.adjoints.proetaleRight v).obj
          ((ImmersionProjectionComparison.comparison A X).obj M.obj)) :=
  AlgebraicGeometry.ProEtale.siteComparisonEvaluationHom (ModuleCat.{u + 1} A) S P
      ((z.adjoints.etaleRight v).obj M.obj) ≫
    ((AlgebraicGeometry.ProEtale.derivedHom (ModuleCat.{u + 1} A) S).obj
      (op ((ImmersionProjectionComparison.comparison A S).obj P))).map (z.gamma.hom.app M)

/-- The exact equation and all its conditional invertibility clauses at the chosen inputs.
Source: blueprint finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-stratum-hom-comparison-mate). -/
def IdentityAndIsomorphisms (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V X : Scheme.{u}} [IsNoetherian X] (c : S ⟶ V) (v : V ⟶ X)
    [IsClosedImmersion c] [IsOpenImmersion v] [QuasiCompact (c ≫ v)]
    (z : AlgebraicGeometry.ProEtale.LocallyClosedExceptionalComparison A c v)
    (P : Etale.D A S) (M : AlgebraicGeometry.Etale.BoundedConstructibleDerivedCategory A X)
    (χe : Etale.HomIso A c v z.adjoints) (χp : ProEtale.HomIso A c v z.adjoints)
    (hK : DerivedCategory.TStructure.t.plus
      (Etale.hom A S P ((z.adjoints.etaleRight v).obj M.obj))) : Prop :=
  (AlgebraicGeometry.ProEtale.siteComparisonEvaluationHom (ModuleCat.{u + 1} A) X
        ((AlgebraicGeometry.ProEtale.locallyClosedEtaleExtension A c v).obj P) M.obj ≫
      homChange A c v P M.obj ≫
      χp.hom.app (op ((ImmersionProjectionComparison.comparison A S).obj P),
        (ImmersionProjectionComparison.comparison A X).obj M.obj) =
    (ImmersionProjectionComparison.comparison A X).map (χe.hom.app (op P, M.obj)) ≫
      directImageMate A (c ≫ v) ⟨_, hK⟩ ≫
      (AlgebraicGeometry.ProEtale.lowerStar (ModuleCat.{u + 1} A) (c ≫ v)
        ).rightDerivedFunctor.map (stratumMap A c v z P M)) ∧
  (IsIso (AlgebraicGeometry.ProEtale.siteComparisonEvaluationHom (ModuleCat.{u + 1} A) S P
      ((z.adjoints.etaleRight v).obj M.obj)) →
    IsIso (AlgebraicGeometry.ProEtale.siteComparisonEvaluationHom (ModuleCat.{u + 1} A) X
      ((AlgebraicGeometry.ProEtale.locallyClosedEtaleExtension A c v).obj P) M.obj) ∧
    IsIso (homChange A c v P M.obj) ∧
    IsIso (χp.hom.app (op ((ImmersionProjectionComparison.comparison A S).obj P),
      (ImmersionProjectionComparison.comparison A X).obj M.obj)) ∧
    IsIso ((ImmersionProjectionComparison.comparison A X).map (χe.hom.app (op P, M.obj))) ∧
    IsIso (directImageMate A (c ≫ v) ⟨_, hK⟩) ∧
    IsIso (stratumMap A c v z P M) ∧
    IsIso ((AlgebraicGeometry.ProEtale.lowerStar (ModuleCat.{u + 1} A) (c ≫ v)
      ).rightDerivedFunctor.map (stratumMap A c v z P M)))

/-- The conclusion for a finite coefficient ring; all auxiliary maps above are canonical data.
Source: blueprint finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-stratum-hom-comparison-mate). -/
def Conclusion (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V X : Scheme.{u}} [IsNoetherian X] (c : S ⟶ V) (v : V ⟶ X)
    [IsClosedImmersion c] [IsOpenImmersion v] [QuasiCompact (c ≫ v)] : Prop :=
  ∀ (z : AlgebraicGeometry.ProEtale.LocallyClosedExceptionalComparison A c v)
    (L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)),
    Scheme.IsFiniteLocallyConstantSheaf L →
    (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S),
      Module.Flat A (((Scheme.pointSmallEtale s).ulift.{u + 1}.sheafFiber
        (A := ModuleCat.{u + 1} A)).obj L)) →
    ∀ M : AlgebraicGeometry.Etale.BoundedConstructibleDerivedCategory A X,
    AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible A S
      ((z.adjoints.etaleRight v).obj M.obj) →
    ∃ χe : Etale.HomIso A c v z.adjoints, ∃ χp : ProEtale.HomIso A c v z.adjoints,
      Etale.Normalized A c v z.adjoints χe ∧ ProEtale.Normalized A c v z.adjoints χp ∧
      ∃ hK : DerivedCategory.TStructure.t.plus
        (Etale.hom A S (ImmersionProjectionComparison.single A L)
          ((z.adjoints.etaleRight v).obj M.obj)),
        IdentityAndIsomorphisms A c v z (ImmersionProjectionComparison.single A L) M χe χp hK

end AlgebraicGeometry.StratumHomComparisonMate
