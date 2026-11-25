/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
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
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
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
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
public import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
public import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Cones
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
public import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import Mathlib.Algebra.Homology.Localization
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
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
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
public import WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Unique

public import WeilConjectures.Algebra.Homology.ScalarInternalHomData
/-! # Internal Hom and arbitrary changes of ring-sheaf coefficients

Source: Bhatt--Scholze, Remark 6.8.15 (ambient derived operations);
Stacks Project, sites-cohomology.tex, Tags 07A6, 07A4, 08J9, 08JA and 0D6D,
and derived.tex, Tag 05RT
(blueprint: def-sfb-scalar-hom-comparison-data).
This is the auxiliary scalar-adjunction comparison extracted from the final
paragraph of proposition-six-operations-dctf--15 in the current blueprint.
Every comparison is normalized on actual K-flat tensors. In particular these
are ordinary unbounded module derived categories, with no flatness or
perfectness assumption on a coefficient map or a derived input.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe c v r w
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
open SheafOfModules
attribute [local irreducible] monoidalCategory derivedInternalHomOfUniverses
namespace SheafOfModules

variable {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [HasSheafify J AddCommGrpCat.{r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]

variable {J} {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S)

variable [HasDerivedCategory.{w} (scalarModules J R)]
  [HasDerivedCategory.{w} (scalarModules J S)]

end SheafOfModules

namespace CategoryTheory

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [∀ R : Sheaf J CommRingCat.{max c v r}, HasDerivedCategory.{w} (scalarModules J R)]

variable {J} (M : ScalarHomModels.{c, v, r, w} J)
  {R S T : Sheaf J CommRingCat.{max c v r}}

/-- Actual scalar-unit sections used by every tensor normalization below.
Source: Stacks 07A6 (blueprint: def-sfb-scalar-hom-comparison-data). -/
noncomputable def scalarHomUnitSection (a : R ⟶ S) (P : scalarModules J R)
    (V : Cᵒᵖ) (x : P.val.obj V) : ((M.scalar a).extension.obj P).val.obj V :=
  ((M.scalar a).ordinaryAdjunction.unit.app P).val.app V x

attribute [local irreducible] scalarPairComplexComparison
  coefficientTotalTensor CoefficientTensorModels.iso

/-- The representative square for a scalar tensor comparison, packaged to keep
structure projections from repeatedly elaborating total-complex instances.
Source: Stacks 07A4 (blueprint: def-sfb-scalar-hom-comparison-data). -/
def ScalarHomTensorNormalization (a : R ⟶ S)
    (hE : ∀ (P : CochainComplex (scalarModules J R) ℤ),
      CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P →
        CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := S)
          ((scalarComplex (M.scalar a).extension (M.scalar a).extension_additive).obj P))
    (e : ∀ (P Q : CochainComplex (scalarModules J R) ℤ),
      (scalarComplex (M.scalar a).extension (M.scalar a).extension_additive).obj
          ((coefficientTotalTensor.{r, c, v} J R).obj (P, Q)) ≅
        (coefficientTotalTensor.{r, c, v} J S).obj
          ((scalarComplex (M.scalar a).extension (M.scalar a).extension_additive).obj P,
           (scalarComplex (M.scalar a).extension (M.scalar a).extension_additive).obj Q))
    (μ : (M.closed R).tensor ⋙ (M.scalar a).derived ≅
      ((M.scalar a).derived.prod (M.scalar a).derived) ⋙ (M.closed S).tensor) : Prop :=
  ∀ (P Q : CochainComplex (scalarModules J R) ℤ)
    (hp : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
    (hq : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) Q),
    (M.scalar a).derived.map
        ((CoefficientTensorModels.iso.{r, c, v, w} J R (M.closed R) (M.model R)
          P Q hp hq).hom) ≫
      μ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
        (M.closed S).tensor.map (Prod.mkHom
          (scalarPairComplexComparison (M.scalar a).extension (M.scalar a).extension_additive
            (M.scalar a).derived (M.scalar a).counit P)
          (scalarPairComplexComparison (M.scalar a).extension (M.scalar a).extension_additive
            (M.scalar a).derived (M.scalar a).counit Q)) =
      scalarPairComplexComparison (M.scalar a).extension (M.scalar a).extension_additive
          (M.scalar a).derived (M.scalar a).counit
            ((coefficientTotalTensor.{r, c, v} J R).obj (P, Q)) ≫
        DerivedCategory.Q.map (e P Q).hom ≫
          (CoefficientTensorModels.iso.{r, c, v, w} J S (M.closed S) (M.model S)
            _ _ (hE P hp) (hE Q hq)).hom

attribute [local irreducible] ScalarHomTensorNormalization

set_option backward.isDefEq.respectTransparency.types true in
/-- Strong scalar tensor comparison, retaining its actual pure-tensor normalization
before and after passage to the derived category.
Source: Stacks 07A4 and 0D6D
(blueprint: def-sfb-scalar-hom-comparison-data). -/
structure ScalarHomTensorComparison (a : R ⟶ S) where
  /-- Scalar extension carries K-flat complexes to K-flat complexes. -/
  preservesKFlat : ∀ (P : CochainComplex (scalarModules J R) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P →
      CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := S)
        ((scalarComplex (M.scalar a).extension (M.scalar a).extension_additive).obj P)
  /-- The actual chain tensor comparison, with the differential signs retained. -/
  complexIso : ∀ (P Q : CochainComplex (scalarModules J R) ℤ),
    (scalarComplex (M.scalar a).extension (M.scalar a).extension_additive).obj
        ((coefficientTotalTensor.{r, c, v} J R).obj (P, Q)) ≅
      (coefficientTotalTensor.{r, c, v} J S).obj
        ((scalarComplex (M.scalar a).extension (M.scalar a).extension_additive).obj P,
         (scalarComplex (M.scalar a).extension (M.scalar a).extension_additive).obj Q)
  /-- It sends 1 tensor (x tensor y) to (1 tensor x) tensor (1 tensor y). -/
  generators : ∀ (P Q : CochainComplex (scalarModules J R) ℤ)
    (p q k : ℤ) (h : p + q = k) (V : Cᵒᵖ)
    (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V),
    ((complexIso P Q).hom.f k).val.app V
        (scalarHomUnitSection M a _ V
          (coefficientTensorGenerator.{r, c, v} J R P Q p q k h V x y)) =
      coefficientTensorGenerator.{r, c, v} J S
        ((scalarComplex (M.scalar a).extension (M.scalar a).extension_additive).obj P)
        ((scalarComplex (M.scalar a).extension (M.scalar a).extension_additive).obj Q)
        p q k h V (scalarHomUnitSection M a _ V x) (scalarHomUnitSection M a _ V y)
  /-- The natural derived strong tensor comparison. -/
  iso : (M.closed R).tensor ⋙ (M.scalar a).derived ≅
    ((M.scalar a).derived.prod (M.scalar a).derived) ⋙ (M.closed S).tensor
  /-- Its defining square on the actual K-flat representatives. -/
  normalization : ScalarHomTensorNormalization M a preservesKFlat complexIso iso

/-- The actual source bifunctor U RHom_S(F(-),-).
Source: Stacks 07A6 and 08J9 (blueprint: def-sfb-scalar-hom-comparison-data). -/
noncomputable def scalarHomSource (a : R ⟶ S) :
    (DerivedCategory (scalarModules J R))ᵒᵖ × DerivedCategory (scalarModules J S) ⥤
      DerivedCategory (scalarModules J R) :=
  ((M.scalar a).derived.op.prod (𝟭 _)) ⋙
    derivedInternalHomOfUniverses.{c, v, r, w} J S ⋙ scalarDerivedRestriction a

/-- The actual target bifunctor RHom_R(-,U(-)).
Source: Stacks 07A6 and 08J9 (blueprint: def-sfb-scalar-hom-comparison-data). -/
noncomputable def scalarHomTarget (a : R ⟶ S) :
    (DerivedCategory (scalarModules J R))ᵒᵖ × DerivedCategory (scalarModules J S) ⥤
      DerivedCategory (scalarModules J R) :=
  ((𝟭 _).prod (scalarDerivedRestriction a)) ⋙
    derivedInternalHomOfUniverses.{c, v, r, w} J R

/-- The five canonical representing Hom bijections, in the order of the node's proof.
Source: Stacks 07A6, 07A4 and 08J9
(blueprint: def-sfb-scalar-hom-comparison-data). -/
noncomputable def scalarHomBijection (a : R ⟶ S) (μ : ScalarHomTensorComparison M a)
    (A K : DerivedCategory (scalarModules J R)) (N : DerivedCategory (scalarModules J S)) :
    (A ⟶ (scalarHomSource M a).obj (op K, N)) ≃
      (A ⟶ (scalarHomTarget.{c, v, r, w} a).obj (op K, N)) :=
  Equiv.trans
    ((M.scalar a).adjunction.homEquiv A
      ((derivedInternalHomOfUniverses.{c, v, r, w} J S).obj
        (op ((M.scalar a).derived.obj K), N))).symm
    (Equiv.trans
      ((M.closed S).transpose ((M.scalar a).derived.obj A)
        ((M.scalar a).derived.obj K) N).symm
      (Equiv.trans (Iso.homCongr (μ.iso.app (A, K)).symm (Iso.refl N))
        (Equiv.trans ((M.scalar a).adjunction.homEquiv ((M.closed R).tensor.obj (A, K)) N)
          ((M.closed R).transpose A K ((scalarDerivedRestriction a).obj N)))))

/-- The canonical lax tensor map on scalar restriction, the counit mate of the
strong scalar extension tensor comparison.
Source: Stacks 07A4 and 07A6 (blueprint: def-sfb-scalar-hom-comparison-data). -/
noncomputable def scalarHomRestrictionTensor (a : R ⟶ S) (μ : ScalarHomTensorComparison M a)
    (H V : DerivedCategory (scalarModules J S)) :
    (M.closed R).tensor.obj
        ((scalarDerivedRestriction a).obj H, (scalarDerivedRestriction a).obj V) ⟶
      (scalarDerivedRestriction a).obj ((M.closed S).tensor.obj (H, V)) :=
  (M.scalar a).adjunction.unit.app _ ≫
    (scalarDerivedRestriction a).map
      (μ.iso.hom.app _ ≫ (M.closed S).tensor.map
        (Prod.mkHom ((M.scalar a).adjunction.counit.app H)
          ((M.scalar a).adjunction.counit.app V)))

/-- Restricted S-linear evaluation after the actual scalar-extension unit.
Source: Stacks 07A6 and 08J9 (blueprint: def-sfb-scalar-hom-comparison-data). -/
noncomputable def scalarHomRestrictedEvaluation (a : R ⟶ S) (μ : ScalarHomTensorComparison M a)
    (K : DerivedCategory (scalarModules J R)) (N : DerivedCategory (scalarModules J S)) :
    (M.closed R).tensor.obj ((scalarHomSource M a).obj (op K, N), K) ⟶
      (scalarDerivedRestriction a).obj N :=
  (M.closed R).tensor.map
      (Prod.mkHom (𝟙 _) ((M.scalar a).adjunction.unit.app K)) ≫
    scalarHomRestrictionTensor M a μ
      ((derivedInternalHomOfUniverses.{c, v, r, w} J S).obj
        (op ((M.scalar a).derived.obj K), N)) ((M.scalar a).derived.obj K) ≫
      (scalarDerivedRestriction a).map ((M.closed S).evaluation ((M.scalar a).derived.obj K) N)

/-- Termwise restriction composes by the identity on the underlying module sheaves.
Source: Stacks 0D6D and 07A6 (blueprint: def-sfb-scalar-hom-comparison-data). -/
noncomputable def scalarHomOrdinaryRestrictionComp (a : R ⟶ S) (b : S ⟶ T) :
    scalarRestriction (a ≫ b) ≅ scalarRestriction b ⋙ scalarRestriction a :=
  Iso.refl _

/-- The canonical composition comparison for actual derived scalar restriction.
Source: Stacks 0D6D and 07A6 (blueprint: def-sfb-scalar-hom-comparison-data). -/
noncomputable def scalarHomRestrictionComp (a : R ⟶ S) (b : S ⟶ T) :
    scalarDerivedRestriction (a ≫ b) ≅
      scalarDerivedRestriction b ⋙ scalarDerivedRestriction a :=
  Functor.mapDerivedCategoryNatIso (scalarHomOrdinaryRestrictionComp.{c, v, r} a b) ≪≫
    (Functor.mapDerivedCategoryCompIso (scalarRestriction b) (scalarRestriction a)).symm

/-- Identity coefficient restriction is the identity on the underlying module sheaves.
Source: Stacks 07A6 (blueprint: def-sfb-scalar-hom-comparison-data). -/
noncomputable def scalarHomOrdinaryRestrictionId (R : Sheaf J CommRingCat.{max c v r}) :
    scalarRestriction (𝟙 R) ≅ 𝟭 (scalarModules J R) :=
  Iso.refl _

/-- The canonical identity comparison for actual derived scalar restriction.
Source: Stacks 07A6 (blueprint: def-sfb-scalar-hom-comparison-data). -/
noncomputable def scalarHomRestrictionId (R : Sheaf J CommRingCat.{max c v r}) :
    scalarDerivedRestriction (𝟙 R) ≅ 𝟭 (DerivedCategory (scalarModules J R)) :=
  Functor.mapDerivedCategoryNatIso (scalarHomOrdinaryRestrictionId.{c, v, r} R) ≪≫
    Functor.mapDerivedCategoryIdIso _

/-- The canonical scalar extension composition comparison, uniquely fixed by units.
On K-flat representatives it is t tensor (s tensor x) mapped to t b(s) tensor x;
this is the unique left-adjoint comparison for the actual restriction comparison.
Source: Stacks 0D6D and 07A6 (blueprint: def-sfb-scalar-hom-comparison-data). -/
noncomputable def scalarHomExtensionComp (a : R ⟶ S) (b : S ⟶ T) :
    (M.scalar a).derived ⋙ (M.scalar b).derived ≅ (M.scalar (a ≫ b)).derived :=
  Adjunction.leftAdjointUniq ((M.scalar a).adjunction.comp (M.scalar b).adjunction)
    ((M.scalar (a ≫ b)).adjunction.ofNatIsoRight (scalarHomRestrictionComp.{c, v, r, w} a b))

/-- The unit-normalized identity comparison for scalar extension.
Source: Stacks 07A6 (blueprint: def-sfb-scalar-hom-comparison-data). -/
noncomputable def scalarHomExtensionId (R : Sheaf J CommRingCat.{max c v r}) :
    (M.scalar (𝟙 R)).derived ≅ 𝟭 (DerivedCategory (scalarModules J R)) :=
  Adjunction.leftAdjointUniq
    ((M.scalar (𝟙 R)).adjunction.ofNatIsoRight
      (scalarHomRestrictionId.{c, v, r, w} R)) Adjunction.id

/-- Every clause of the scalar internal-Hom comparison, with canonical maps fixed.
Naturality is encoded by the natural isomorphism of the two actual bifunctors.
Evaluation and representing Hom bijections uniquely determine it. The tower and
identity equations include all necessary coefficient transports explicitly.
Source: Stacks 07A6, 07A4, 08J9, 08JA, 0D6D and 05RT
(blueprint: def-sfb-scalar-hom-comparison-data). -/
structure ScalarInternalHomAdjunction
    (μ : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S),
      ScalarHomTensorComparison M a) where
  /-- The comparison is natural contravariantly in K and covariantly in N. -/
  iso : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S),
    scalarHomSource M a ≅ scalarHomTarget.{c, v, r, w} a
  /-- Its tensor-Hom transpose is restricted evaluation after the scalar unit. -/
  evaluation : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)
    (K : DerivedCategory (scalarModules J R)) (N : DerivedCategory (scalarModules J S)),
    ((M.closed R).transpose _ K ((scalarDerivedRestriction a).obj N)).symm
      ((iso a).hom.app (op K, N)) = scalarHomRestrictedEvaluation M a (μ a) K N
  /-- Evaluation normalization characterizes the isomorphism uniquely. -/
  unique : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)
    (β : scalarHomSource M a ≅ scalarHomTarget.{c, v, r, w} a),
    (∀ (K : DerivedCategory (scalarModules J R)) (N : DerivedCategory (scalarModules J S)),
      ((M.closed R).transpose _ K ((scalarDerivedRestriction a).obj N)).symm
        (β.hom.app (op K, N)) = scalarHomRestrictedEvaluation M a (μ a) K N) → β = iso a
  /-- Equivalently, it induces the specified five representing Hom bijections. -/
  representing : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)
    (A K : DerivedCategory (scalarModules J R)) (N : DerivedCategory (scalarModules J S))
    (t : A ⟶ (scalarHomSource M a).obj (op K, N)),
    scalarHomBijection M a (μ a) A K N t = t ≫ (iso a).hom.app (op K, N)
  /-- The direct and successive comparisons agree along every coefficient tower. -/
  composition : ∀ {R S T : Sheaf J CommRingCat.{max c v r}}
    (a : R ⟶ S) (b : S ⟶ T)
    (K : DerivedCategory (scalarModules J R)) (N : DerivedCategory (scalarModules J T)),
    (iso (a ≫ b)).hom.app (op K, N) ≫
        (derivedInternalHomOfUniverses.{c, v, r, w} J R).map
          (Prod.mkHom (𝟙 (op K)) ((scalarHomRestrictionComp.{c, v, r, w} a b).hom.app N)) =
      (scalarHomRestrictionComp.{c, v, r, w} a b).hom.app
          ((derivedInternalHomOfUniverses.{c, v, r, w} J T).obj
            (op ((M.scalar (a ≫ b)).derived.obj K), N)) ≫
        (scalarDerivedRestriction a).map ((scalarDerivedRestriction b).map
          ((derivedInternalHomOfUniverses.{c, v, r, w} J T).map
            (Prod.mkHom ((scalarHomExtensionComp M a b).hom.app K).op (𝟙 N)))) ≫
          (scalarDerivedRestriction a).map
            ((iso b).hom.app (op ((M.scalar a).derived.obj K), N)) ≫
              (iso a).hom.app (op K, (scalarDerivedRestriction b).obj N)
  /-- The identity coefficient comparison is the identity under the canonical transports. -/
  identity : ∀ (R : Sheaf J CommRingCat.{max c v r})
    (K N : DerivedCategory (scalarModules J R)),
    (iso (𝟙 R)).hom.app (op K, N) ≫
        (derivedInternalHomOfUniverses.{c, v, r, w} J R).map
          (Prod.mkHom (𝟙 (op K)) ((scalarHomRestrictionId.{c, v, r, w} R).hom.app N)) =
      (scalarHomRestrictionId.{c, v, r, w} R).hom.app
          ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj
            (op ((M.scalar (𝟙 R)).derived.obj K), N)) ≫
        (derivedInternalHomOfUniverses.{c, v, r, w} J R).map
          (Prod.mkHom ((scalarHomExtensionId M R).inv.app K).op (𝟙 N))
  /-- Exact scalar restriction detects isomorphisms of all unbounded derived objects. -/
  conservative : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)
    {N N' : DerivedCategory (scalarModules J S)} (f : N ⟶ N'),
    IsIso ((scalarDerivedRestriction a).map f) → IsIso f

end CategoryTheory
