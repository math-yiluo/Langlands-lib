/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SemilinearGeometryDerived
public import WeilConjectures.AlgebraicGeometry.SemilinearGeometryCore
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedCalculusSupplement
public import WeilConjectures.AlgebraicGeometry.SemilinearSystemModels
public import WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
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
public import WeilConjectures.CategoryTheory.RingedSiteModules
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
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
public import WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.CategoryTheory.Sites.CoverPreserving
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import WeilConjectures.AlgebraicGeometry.SemilinearModuleAdjunction
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainModuleAdjunction
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearOrdinaryDirectSystem
import Mathlib.CategoryTheory.Adjunction.Additive

/-! # Ordinary termwise geometric realization

Source: Zheng Construction 4.1 and the paragraph before Lemma 4.10;
Stacks 03D2 and 03D7.
(blueprint: lem-coef-semilinear-ordinary-geometric-realization)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false
universe c v r
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.SemilinearSections
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)
  {C' : Type c} [Category.{v} C'] [EssentiallySmall.{max c v r} C']
  (J' : GrothendieckTopology C')
  (uInv : Sheaf J (Type (max c v r)) ⥤ Sheaf J' (Type (max c v r)))
  (uPush : Sheaf J' (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
  (adjSet : uInv ⊣ uPush)

/-- Ordinary module operations, including their actual horizontal transitions.
This interface contains no derived functor, derived evaluation or tensor comparison.
Source: Zheng Construction 4.1 and the paragraph before Lemma 4.10.
(blueprint: lem-coef-semilinear-ordinary-geometric-realization). -/
structure GeometryOrdinary where
  /-- The inverse-image coefficient sheaves C_n. -/
  coefficients : ℕ → Sheaf J' CommRingCat.{max c v r}
  /-- Their inverse-image transitions. -/
  coefficientTransition : ∀ n : ℕ, coefficients (n + 1) ⟶ coefficients n
  /-- Algebraic inverse image, with actual ring/module operations and underlying sheaves. -/
  inverseImage : ∀ n : ℕ, SheafOfModules.AlgebraicInverseImage uInv (B n) (coefficients n)
  /-- The transitions are u-inverse-image of the supplied tau maps. -/
  coefficient_compatibility : ∀ n : ℕ,
    uInv.map ((sheafCompose J (CategoryTheory.forget CommRingCat.{max c v r})).map (τ n)) ≫
        (inverseImage n).ringUnderlying.hom =
      (inverseImage (n + 1)).ringUnderlying.hom ≫
        (sheafCompose J' (CategoryTheory.forget CommRingCat.{max c v r})).map
          (coefficientTransition n)
  /-- Levelwise exact inverse image. -/
  [levelAdditive : ∀ n : ℕ, (inverseImage n).modules.Additive]
  /-- Left exactness of inverse image of modules. -/
  [levelLimits : ∀ n : ℕ, PreservesFiniteLimits (inverseImage n).modules]
  /-- Right exactness of inverse image of modules. -/
  [levelColimits : ∀ n : ℕ, PreservesFiniteColimits (inverseImage n).modules]
  /-- Ordinary direct image at each coefficient level. -/
  levelPush : ∀ n : ℕ, Mod.{c, v, max c v r} J' (coefficients n) ⥤ Mod.{c, v, max c v r} J (B n)
  /-- Its ordinary adjunction. -/
  levelAdjunction : ∀ n : ℕ, (inverseImage n).modules ⊣ levelPush n
  /-- The underlying set-sheaf direct image is the given uPush. -/
  levelPushUnderlying : ∀ n : ℕ,
    levelPush n ⋙ underlying.{c, v, r} J (B n) ≅
      underlying.{c, v, r} J' (coefficients n) ⋙ uPush
  /-- The module adjunction is normalized by the original topos unit. -/
  level_unit_underlying : ∀ (n : ℕ) (M : Mod.{c, v, max c v r} J (B n)),
    (underlying.{c, v, r} J (B n)).map ((levelAdjunction n).unit.app M) ≫
        (levelPushUnderlying n).hom.app ((inverseImage n).modules.obj M) ≫
        uPush.map ((inverseImage n).moduleUnderlying.hom.app M) =
      adjSet.unit.app ((underlying.{c, v, r} J (B n)).obj M)
  /-- Additivity of direct image. -/
  [levelPushAdditive : ∀ n : ℕ, (levelPush n).Additive]
  /-- Ordinary inverse image on systems. -/
  pull : Systems.{c, v, max c v r} J B τ ⥤ Systems.{c, v, max c v r} J' coefficients
    coefficientTransition
  /-- It is the levelwise inverse image, on modules and maps. -/
  ordinaryPullEvaluation : ∀ n : ℕ,
    pull ⋙ evaluation.{c, v, max c v r} J' coefficients coefficientTransition n ≅
      evaluation.{c, v, max c v r} J B τ n ⋙ (inverseImage n).modules
  /-- Additivity and exactness on systems. -/
  [pullAdditive : pull.Additive]
  /-- Inverse image preserves finite limits. -/
  [pullLimits : PreservesFiniteLimits pull]
  /-- Inverse image preserves finite colimits. -/
  [pullColimits : PreservesFiniteColimits pull]
  /-- The ordinary system right adjoint. -/
  push : Systems.{c, v, max c v r} J' coefficients coefficientTransition ⥤ Systems.{c, v, max c v
    r} J B τ
  /-- The system adjunction before deriving. -/
  ordinaryAdjunction : pull ⊣ push
  /-- Additivity of system direct image. -/
  [pushAdditive : push.Additive]
  /-- The chosen ordinary realization acts as the identity on the actual
  component section carriers. This rules out twisting the evaluation by a sign. -/
  ordinaryPullEvaluation_sections : ∀ (n : ℕ) (M : Systems.{c, v, max c v r} J B τ)
    (U : C'ᵒᵖ)
    (x : ((evaluation.{c, v, max c v r} J' coefficients coefficientTransition n).obj
      (pull.obj M)).val.obj U),
    HEq ((((ordinaryPullEvaluation n).hom.app M).val.app U) x) x
  /-- Ordinary direct image has its actual componentwise realization. -/
  ordinaryPushEvaluation : ∀ n : ℕ,
    push ⋙ evaluation.{c, v, max c v r} J B τ n ≅ evaluation.{c, v, max c v r} J' coefficients
      coefficientTransition n ⋙ levelPush n
  /-- The ordinary push evaluation is the identity on the component carriers. -/
  ordinaryPushEvaluation_sections : ∀ (n : ℕ)
    (M : Systems.{c, v, max c v r} J' coefficients coefficientTransition) (U : Cᵒᵖ)
    (x : ((evaluation.{c, v, max c v r} J B τ n).obj (push.obj M)).val.obj U),
    HEq ((((ordinaryPushEvaluation n).hom.app M).val.app U) x) x
  /-- The ordinary system unit is the level unit under these realizations. -/
  ordinary_unit_evaluation : ∀ (n : ℕ) (M : Systems.{c, v, max c v r} J B τ),
    (evaluation.{c, v, max c v r} J B τ n).map (ordinaryAdjunction.unit.app M) ≫
      (ordinaryPushEvaluation n).hom.app (pull.obj M) ≫
      (levelPush n).map ((ordinaryPullEvaluation n).hom.app M) =
        (levelAdjunction n).unit.app ((evaluation.{c, v, max c v r} J B τ n).obj M)
  /-- Restricting coefficient actions commutes with inverse image. -/
  restrictionPullback : ∀ {m n : ℕ} (h : n ≤ m),
    res.{c, v, max c v r} (coefficientMap.{c, v, max c v r} J B τ h) ⋙ (inverseImage m).modules ≅
      (inverseImage n).modules ⋙ res.{c, v, max c v r} (coefficientMap.{c, v, max c v r} J'
        coefficients coefficientTransition h)
  /-- The ordinary restriction comparison is the identity on the inverse-image
  underlying sheaf; this excludes an unrelated scalar or sign automorphism. -/
  restrictionPullback_underlying : ∀ {m n : ℕ} (h : n ≤ m)
    (M : Mod.{c, v, max c v r} J (B n)),
    (underlying.{c, v, r} J' (coefficients m)).map ((restrictionPullback h).hom.app M) ≫
      (inverseImage n).moduleUnderlying.hom.app M =
        (inverseImage m).moduleUnderlying.hom.app ((res.{c, v, max c v r} (coefficientMap.{c, v,
          max c v r} J B τ h)).obj M)
  /-- Termwise inverse image carries the horizontal transition of the actual
  system to the coefficient-restriction inverse image of that transition.
  This equation is imposed before taking complexes or localizing; specifying
  evaluation on component objects alone does not specify horizontal maps. -/
  ordinaryPullTransition : ∀ {m n : ℕ} (h : n ≤ m)
    (M : Systems.{c, v, max c v r} J B τ),
    (transition.{c, v, max c v r} J' coefficients coefficientTransition h).app (pull.obj M) ≫
        (res.{c, v, max c v r} (coefficientMap.{c, v, max c v r} J'
          coefficients coefficientTransition h)).map ((ordinaryPullEvaluation n).hom.app M) =
      (ordinaryPullEvaluation m).hom.app M ≫
        (inverseImage m).modules.map
          ((transition.{c, v, max c v r} J B τ h).app M) ≫
        (restrictionPullback h).hom.app ((evaluation.{c, v, max c v r} J B τ n).obj M)

attribute [instance] GeometryOrdinary.levelAdditive GeometryOrdinary.levelLimits
  GeometryOrdinary.levelColimits GeometryOrdinary.levelPushAdditive
  GeometryOrdinary.pullAdditive GeometryOrdinary.pullLimits GeometryOrdinary.pullColimits
  GeometryOrdinary.pushAdditive

variable (O : GeometryOrdinary.{c, v, r} J B τ J' uInv uPush adjSet)

/-- Exact pull evaluation is the localization of the ordinary evaluation comparison.
Source: Zheng Construction 4.1; localization of exact functors.
(blueprint: lem-coef-semilinear-ordinary-geometric-realization). -/
def geometryPullEvaluation (n : ℕ) :
    O.pull.mapDerivedCategory ⋙ e.{c, v, max c v r} J' O.coefficients
        O.coefficientTransition n ≅
      e.{c, v, max c v r} J B τ n ⋙
        derivedExact.{c, v, max c v r, c, v} J J' (B n) (O.coefficients n)
          (O.inverseImage n).modules :=
  (Functor.mapDerivedCategoryCompIso _ _) ≪≫
    Functor.mapDerivedCategoryNatIso (O.ordinaryPullEvaluation n) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm

/-- Add the chosen target calculus and canonical unbounded derived adjunction.
All ordinary data are retained verbatim; the two resolution instances are supplied separately.
Source: Zheng Construction 4.1; Stacks 079P and 07A6.
(blueprint: lem-coef-semilinear-ordinary-geometric-realization). -/
def GeometryOrdinary.toBase
    (target : Data.{c, v, r} J' O.coefficients O.coefficientTransition)
    [∀ n : ℕ, Abelian.HasKInjectiveResolutions (Mod.{c, v, max c v r} J' (O.coefficients n))]
    [Abelian.HasKInjectiveResolutions
      (Systems.{c, v, max c v r} J' O.coefficients O.coefficientTransition)] :
    GeometryBase.{c, v, r} J B τ J' uInv uPush adjSet :=
  { O with
    target := target
    levelKInjective := inferInstance
    systemKInjective := inferInstance
    adjunction := O.ordinaryAdjunction.mapDerivedCategoryRightDerivedAdjunction }

private theorem moduleUnderlying_limits (R : Sheaf J CommRingCat.{max c v r}) :
    PreservesFiniteLimits (underlying.{c, v, r} J R) := by
  let V := sheafCompose J (CategoryTheory.forget AddCommGrpCat.{max c v r})
  have : PreservesFiniteLimits (V ⋙ sheafToPresheaf J (Type (max c v r))) :=
    show PreservesFiniteLimits (sheafToPresheaf J AddCommGrpCat.{max c v r} ⋙
      (Functor.whiskeringRight _ _ _).obj (CategoryTheory.forget AddCommGrpCat.{max c v r}))
      from comp_preservesFiniteLimits _ _
  have : PreservesFiniteLimits V :=
    preservesFiniteLimits_of_reflects_of_preserves _ (sheafToPresheaf J (Type (max c v r)))
  exact comp_preservesFiniteLimits _ _

private theorem algebraicInverse_limits [PreservesFiniteLimits uInv]
    (R : Sheaf J CommRingCat.{max c v r}) (S : Sheaf J' CommRingCat.{max c v r})
    (I : SheafOfModules.AlgebraicInverseImage uInv R S) :
    PreservesFiniteLimits I.modules := by
  have := moduleUnderlying_limits.{c, v, r} J R
  have := moduleUnderlying_limits.{c, v, r} J' S
  have : PreservesFiniteLimits (underlying.{c, v, r} J R ⋙ uInv) :=
    comp_preservesFiniteLimits _ _
  have : PreservesFiniteLimits (I.modules ⋙ underlying.{c, v, r} J' S) :=
    preservesFiniteLimits_of_natIso I.moduleUnderlying.symm
  exact preservesFiniteLimits_of_reflects_of_preserves I.modules
    (underlying.{c, v, r} J' S)

private theorem system_hom_ext {M N : Systems.{c, v, max c v r} J B τ}
    {f g : M ⟶ N}
    (h : ∀ n, (evaluation.{c, v, max c v r} J B τ n).map f =
      (evaluation.{c, v, max c v r} J B τ n).map g) : f = g := by
  ext X x
  exact congrArg (fun q ↦ q.val.app (op X.unop.2) x) (h X.unop.1)

private theorem system_transpose_natural_left
    {F : ℕ → Sheaf J' CommRingCat.{max c v r}} {σ : ∀ n, F (n + 1) ⟶ F n}
    {I : ∀ n, SheafOfModules.AlgebraicInverseImage uInv (B n) (F n)}
    (P : OrdinaryInverseSystem.{c, v, r} J B τ J' uInv F σ I)
    {V : ∀ n, Mod.{c, v, max c v r} J' (F n) ⥤ Mod.{c, v, max c v r} J (B n)}
    (a : ∀ n, (I n).modules ⊣ V n)
    (D : OrdinaryDirectSystem.{c, v, r} J B τ J' uInv F σ I P V a)
    {M M' : Systems.{c, v, max c v r} J B τ} (f : M ⟶ M')
    (N : Systems.{c, v, max c v r} J' F σ) (g : P.pull.obj M' ⟶ N) :
    D.homEquiv M N (P.pull.map f ≫ g) = f ≫ D.homEquiv M' N g := by
  apply system_hom_ext.{c, v, r} J B τ
  intro n
  apply (cancel_mono ((D.component n).hom.app N)).mp
  rw [D.homEquiv_component]
  simp only [Functor.map_comp, Category.assoc]
  rw [D.homEquiv_component]
  have hn := (P.component n).inv.naturality f
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc, ← hn, Category.assoc, (a n).homEquiv_naturality_left]

private theorem system_transpose_natural_right
    {F : ℕ → Sheaf J' CommRingCat.{max c v r}} {σ : ∀ n, F (n + 1) ⟶ F n}
    {I : ∀ n, SheafOfModules.AlgebraicInverseImage uInv (B n) (F n)}
    (P : OrdinaryInverseSystem.{c, v, r} J B τ J' uInv F σ I)
    {V : ∀ n, Mod.{c, v, max c v r} J' (F n) ⥤ Mod.{c, v, max c v r} J (B n)}
    (a : ∀ n, (I n).modules ⊣ V n)
    (D : OrdinaryDirectSystem.{c, v, r} J B τ J' uInv F σ I P V a)
    (M : Systems.{c, v, max c v r} J B τ)
    {N N' : Systems.{c, v, max c v r} J' F σ}
    (f : P.pull.obj M ⟶ N) (g : N ⟶ N') :
    D.homEquiv M N' (f ≫ g) = D.homEquiv M N f ≫ D.push.map g := by
  apply system_hom_ext.{c, v, r} J B τ
  intro n
  apply (cancel_mono ((D.component n).hom.app N')).mp
  rw [D.homEquiv_component]
  simp only [Functor.map_comp, Category.assoc]
  have hn := (D.component n).hom.naturality g
  dsimp only [Functor.comp_map] at hn
  rw [hn]
  rw [← Category.assoc ((evaluation.{c, v, max c v r} J B τ n).map
    (D.homEquiv M N f)), D.homEquiv_component]
  simp only [Functor.map_comp, Category.assoc, (a n).homEquiv_naturality_right]

/-- The termwise geometric construction on ordinary strict systems.
Source: Zheng Construction 4.1 and the paragraph before Lemma 4.10;
Stacks 03D2 and 03D7.
(blueprint: lem-coef-semilinear-ordinary-geometric-realization).

Proof: use the supplied coefficient tower and algebraic inverse images, whose
ring operations and underlying sheaf maps are already fixed. For a module
system, apply module inverse image at each level. Its horizontal map is inverse image of
the old horizontal map, conjugated by the underlying-sheaf identifications. The universal
addition and scalar diagrams prove that it is semilinear. Identity and composition follow
from those of the old horizontal maps. Define the inverse-image system using exactly
these component carriers, so its evaluation comparison is identity on their sections.
Transport modules along the product-preserving right adjoint with coefficient action
through the transposed ring map. Do this termwise on systems, again using the actual
component carriers. The set-sheaf adjunction restricts to linear maps; the equations for
commuting with horizontal transitions correspond under that same bijection. Thus it
restricts further to a natural bijection of system maps. Its unit evaluated at a level
is the ordinary module unit, and its underlying map is the original topos unit.
Inverse image is additive and preserves finite limits and colimits componentwise.
Finally, restriction of scalars changes only the action, so its inverse-image comparison
is identity on underlying sheaves. The defining horizontal map gives the displayed
ordinary pull-transition equation. No derived assertion is used. -/
theorem semilinearGeometryOrdinary [PreservesFiniteLimits uInv]
    (F : ℕ → Sheaf J' CommRingCat.{max c v r}) (σ : ∀ n : ℕ, F (n + 1) ⟶ F n)
    (I : ∀ n : ℕ, SheafOfModules.AlgebraicInverseImage uInv (B n) (F n))
    (hI : ∀ n : ℕ,
      uInv.map ((sheafCompose J (CategoryTheory.forget CommRingCat.{max c v r})).map (τ n)) ≫
          (I n).ringUnderlying.hom =
        (I (n + 1)).ringUnderlying.hom ≫
          (sheafCompose J' (CategoryTheory.forget CommRingCat.{max c v r})).map (σ n)) :
    Nonempty {O : GeometryOrdinary.{c, v, r} J B τ J' uInv uPush adjSet //
      O.coefficients = F ∧ HEq O.coefficientTransition σ ∧ HEq O.inverseImage I} := by
  classical
  have hlevel (n : ℕ) := normalizedModuleAdjunction_exists (B n) (F n)
    uInv uPush adjSet (I n)
  choose V eV a ha using hlevel
  let (n : ℕ) : PreservesFiniteLimits (I n).modules :=
    algebraicInverse_limits.{c, v, r} J J' uInv (B n) (F n) (I n)
  let (n : ℕ) : PreservesColimits (I n).modules := (a n).leftAdjoint_preservesColimits
  let (n : ℕ) : (I n).modules.Additive :=
    Functor.additive_of_preserves_binary_products _
  let (n : ℕ) : (V n).Additive := (a n).right_adjoint_additive
  obtain ⟨P⟩ := ordinaryInverseSystem_exists.{c, v, r} J B τ J' uInv F σ I hI
  obtain ⟨D⟩ := ordinaryDirectSystem_exists.{c, v, r} J B τ J' uInv F σ I P V a
    hI uPush adjSet eV ha
  let core : Adjunction.CoreHomEquiv P.pull D.push :=
    { homEquiv := D.homEquiv
      homEquiv_naturality_left_symm := by
        intro M M' N f g
        apply (D.homEquiv M N).injective
        rw [Equiv.apply_symm_apply,
          system_transpose_natural_left.{c, v, r} J B τ J' uInv P a D,
          Equiv.apply_symm_apply]
      homEquiv_naturality_right :=
        system_transpose_natural_right.{c, v, r} J B τ J' uInv P a D _ }
  let aSys := Adjunction.mkOfHomEquiv core
  let : PreservesColimits P.pull := aSys.leftAdjoint_preservesColimits
  let : P.pull.Additive := Functor.additive_of_preserves_binary_products _
  let : D.push.Additive := aSys.right_adjoint_additive
  have hunit n (M : Mod.{c, v, max c v r} J (B n)) :
      (underlying.{c, v, r} J (B n)).map ((a n).unit.app M) ≫
          (eV n).hom.app ((I n).modules.obj M) ≫
          uPush.map ((I n).moduleUnderlying.hom.app M) =
        adjSet.unit.app ((underlying.{c, v, r} J (B n)).obj M) := by
    rw [← (a n).homEquiv_id M, ← Category.assoc]
    dsimp only [underlying]
    rw [ha n M ((I n).modules.obj M) (𝟙 _)]
    rw [Adjunction.homEquiv_unit, Category.assoc, ← uPush.map_comp]
    simp
  have hsunit n (M : Systems.{c, v, max c v r} J B τ) :
      (evaluation.{c, v, max c v r} J B τ n).map (aSys.unit.app M) ≫
          (D.component n).hom.app (P.pull.obj M) ≫
          (V n).map ((P.component n).hom.app M) =
        (a n).unit.app ((evaluation.{c, v, max c v r} J B τ n).obj M) := by
    rw [← aSys.homEquiv_id M]
    dsimp only [aSys]
    rw [Adjunction.mkOfHomEquiv_homEquiv]
    change (evaluation.{c, v, max c v r} J B τ n).map
      (D.homEquiv M (P.pull.obj M) (𝟙 _)) ≫ _ ≫ _ = _
    rw [← Category.assoc, D.homEquiv_component, ← (a n).homEquiv_naturality_right]
    simpa using (a n).homEquiv_id ((evaluation J B τ n).obj M)
  refine ⟨⟨
    { coefficients := F
      coefficientTransition := σ
      inverseImage := I
      coefficient_compatibility := hI
      levelPush := V
      levelAdjunction := a
      levelPushUnderlying := eV
      level_unit_underlying := hunit
      pull := P.pull
      ordinaryPullEvaluation := P.component
      push := D.push
      ordinaryAdjunction := aSys
      ordinaryPullEvaluation_sections := P.component_sections
      ordinaryPushEvaluation := D.component
      ordinaryPushEvaluation_sections := D.component_sections
      ordinary_unit_evaluation := hsunit
      restrictionPullback := P.restriction
      restrictionPullback_underlying := P.restriction_underlying
      ordinaryPullTransition := P.transition }, rfl, HEq.rfl, HEq.rfl⟩⟩

end WeilConjectures.SemilinearSections
