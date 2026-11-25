/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.SixFunctors.Etale.Derived.LocallyConstantInvertible
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleIntrinsic
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.AlgebraicGeometry.Flat.FlatConstructibleTensor
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlat
import WeilConjectures.AlgebraicGeometry.Finite.FiniteTensorConstructibleCohomology
import WeilConjectures.Algebra.Homology.FlatSingleDerivedNormalization.FlatSingleDerivedNormalization
import WeilConjectures.Algebra.Homology.Finite.FiniteFreeDualPullback
import WeilConjectures.Algebra.Homology.LineEvaluation.LineEvaluationInversePair
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
import WeilConjectures.Algebra.Homology.RingedKFlatSingleTensorComparison
import Mathlib.Algebra.Homology.HomologicalComplex
import WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Localization.Construction
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Whiskering
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Localization.Prod
import Mathlib.Algebra.Homology.BifunctorFlip
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Homology.KFlatFixedTensor.KFlatFixedTensorTriangulatedSupplement
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.Algebra.Homology.KFlatTensorPreservesQuasiIsoIndependentCoefficients
import WeilConjectures.CategoryTheory.Principal.PrincipalKoszulQuotientTowersSupplement
import WeilConjectures.CategoryTheory.RingedDerivedComparisons.RingedDerivedMonoidalComparisons
import WeilConjectures.Algebra.Homology.Derived.DerivedTensorShiftDescent
import WeilConjectures.Algebra.Homology.PullbackTensorCanonical.PullbackTensorCanonicalShiftUnit
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDerivedPullbackFixed

/-! # Shifted line inverses on the etale and pro-etale sites

## References

* Stacks Project, Tags 0B8Q, 0B8N, 06YQ, 07A4 and 0FNH
* Stacks 07A4 and 0GMX
* Stacks 099R and 0FNH
* Stacks finite coefficient setting
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w d h

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.ProEtale

/-- The canonical comparison for exact inverse image from the etale to the pro-etale
site. This is an abbreviation for the existing left-derived tensor comparison, with its
canonical identifications with termwise exact inverse image. It retains the general
ringed-topos representative normalization and makes no new choice. -/
noncomputable abbrev siteComparisonCanonicalDerivedTensor
    (B : Type v) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    (T : Scheme.{u}) [(comparisonUpperStar B T).PreservesFlat]
    (K : DerivedCategory (Sheaf T.smallEtaleTopology B)) :
    (Etale.derivedTensor B T).obj K ⋙ (comparisonUpperStar B T).mapDerivedCategory ≅
      (comparisonUpperStar B T).mapDerivedCategory ⋙
        (derivedTensor B T).obj ((comparisonUpperStar B T).mapDerivedCategory.obj K) :=
  derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso B K

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ShiftedLineSiteInverse

section Normalization

variable {C : Type v} [Category.{w} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
  [Abelian.HasFunctorialFlatResolution C]

/-- The canonical single-term tensor comparison, obtained from the localization's lax
monoidal comparison and the sole degree-zero tensor summand. No inverse is chosen. -/
def singleTensorMap (L M : C) :
    (DerivedCategory.singleFunctor C 0).obj L ⊗
      (DerivedCategory.singleFunctor C 0).obj M ⟶
        (DerivedCategory.singleFunctor C 0).obj (L ⊗ M) :=
  (tensorIso
    ((DerivedCategory.singleFunctorIsoCompQ C 0).app L ≪≫
      (DerivedCategory.quotientCompQhIso C).symm.app _)
    ((DerivedCategory.singleFunctorIsoCompQ C 0).app M ≪≫
      (DerivedCategory.quotientCompQhIso C).symm.app _)).hom ≫
  Functor.LaxMonoidal.μ (DerivedCategory.Qh (C := C)) _ _ ≫
  DerivedCategory.Qh.map
    ((Functor.Monoidal.μIso (HomotopyCategory.quotient C (.up ℤ)) _ _).hom ≫
      (HomotopyCategory.quotient C (.up ℤ)).map
        ((((CochainComplex.map₂HomologicalComplexObjSingleIso
          (curriedTensor C) L).app _) ≪≫
          ((HomologicalComplex.singleMapHomologicalComplex
            (tensorLeft L) (.up ℤ) 0).app M)).hom)) ≫
  ((DerivedCategory.singleFunctorIsoCompQ C 0).app (L ⊗ M) ≪≫
    (DerivedCategory.quotientCompQhIso C).symm.app _).inv

/-- Evaluation of oppositely shifted degree-zero sheaves. Extract the first shift and
then the second by the signed total-tensor comparisons, cancel their sum, and evaluate
on the sole degree-zero term. In particular the reverse order is specified separately,
without inserting the graded braiding. -/
def evaluation (L M : C) (e : L ⊗ M ⟶ 𝟙_ C) (m : ℤ) :
    ((DerivedCategory.singleFunctor C 0).obj L)⟦m⟧ ⊗
      ((DerivedCategory.singleFunctor C 0).obj M)⟦-m⟧ ⟶ 𝟙_ (DerivedCategory C) :=
  (DerivedCategory.shiftTensorShiftIso C _ _ m (-m)).hom ≫
  (shiftFunctorZero' _ (m + -m) (add_neg_cancel m)).hom.app _ ≫
  singleTensorMap L M ≫ (DerivedCategory.singleFunctor C 0).map e ≫
  (DerivedCategory.singleFunctorObjUnitIso C).hom

end Normalization

section Comparison

variable (B : Type v) [Category.{u + 1} B] [Abelian B]
  [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
  [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
  (T : Scheme.{u})

/-- The existing exact inverse image in the fixed constant-ring presentation. -/
abbrev inverseImage := ProEtale.comparisonUpperStar B T

/-- The termwise derived comparison on the unbounded derived categories. -/
abbrev derivedInverseImage := (inverseImage B T).mapDerivedCategory

/-- The canonical comparison of a pulled internal dual with the dual of the pulled line. -/
def dualComparison (L : Sheaf T.smallEtaleTopology B) :
    (inverseImage B T).obj ((ihom L).obj (𝟙_ _)) ⟶
      (ihom ((inverseImage B T).obj L)).obj (𝟙_ _) :=
  (Functor.LaxMonoidal.ihomComparison (inverseImage B T) L).app (𝟙_ _) ≫
    (ihom ((inverseImage B T).obj L)).map (Functor.OplaxMonoidal.η (inverseImage B T))

/-- Pullback of a sheaf pairing, with the canonical tensor and coefficient-unit maps. -/
def pulledPairing (L M : Sheaf T.smallEtaleTopology B)
    (e : L ⊗ M ⟶ 𝟙_ _) :
    (inverseImage B T).obj L ⊗ (inverseImage B T).obj M ⟶ 𝟙_ _ :=
  Functor.LaxMonoidal.μ (inverseImage B T) L M ≫
    (inverseImage B T).map e ≫ Functor.OplaxMonoidal.η (inverseImage B T)

/-- Canonical comparison on a shifted single sheaf, including its signed shift map. -/
def shiftedSingleComparison (L : Sheaf T.smallEtaleTopology B)
    (m : ℤ) :
    (derivedInverseImage B T).obj (((DerivedCategory.singleFunctor _ 0).obj L)⟦m⟧) ≅
      ((DerivedCategory.singleFunctor _ 0).obj ((inverseImage B T).obj L))⟦m⟧ :=
  ((derivedInverseImage B T).commShiftIso m).app _ ≪≫
    (shiftFunctor _ m).mapIso (((inverseImage B T).mapDerivedCategorySingleFunctor 0).app L)

/-- The derived coefficient-unit comparison, induced from the ordinary unit comparison. -/
def unitComparison : (derivedInverseImage B T).obj (𝟙_ _) ≅ 𝟙_ _ :=
  (derivedInverseImage B T).mapIso (DerivedCategory.singleFunctorObjUnitIso _).symm ≪≫
  ((inverseImage B T).mapDerivedCategorySingleFunctor 0).app _ ≪≫
  (DerivedCategory.singleFunctor _ 0).mapIso
    (asIso (Functor.OplaxMonoidal.η (inverseImage B T))) ≪≫
  DerivedCategory.singleFunctorObjUnitIso _

/-- The commuting square for the specified derived evaluation, using the canonical
K-flat tensor comparison, signed single-shift comparisons, and coefficient-unit comparison. -/
def evaluationComparison [(inverseImage B T).PreservesFlat]
    (L M : Sheaf T.smallEtaleTopology B)
    (e : L ⊗ M ⟶ 𝟙_ _) (m : ℤ) : Prop :=
  (derivedInverseImage B T).map (evaluation L M e m) ≫ (unitComparison B T).hom =
    (ProEtale.siteComparisonCanonicalDerivedTensor
      B T (((DerivedCategory.singleFunctor _ 0).obj L)⟦m⟧)).hom.app
        (((DerivedCategory.singleFunctor _ 0).obj M)⟦-m⟧) ≫
    (tensorIso (shiftedSingleComparison B T L m)
      (shiftedSingleComparison B T M (-m))).hom ≫
    evaluation ((inverseImage B T).obj L) ((inverseImage B T).obj M)
      (pulledPairing B T L M e) m

end Comparison

variable (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})

/-- Finiteness of the prescribed positive-level quotient, transported by the standard
universe lift. -/
instance coefficientFinite (P : WeilConjectures.PurityFiniteSetting.{u}) :
    Finite P.Coefficient :=
  letI : Finite P.Ring := Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension P.level P.level_pos
  inferInstanceAs (Finite (ULift.{u + 1} P.Ring))

/-- The sheaf dual is the existing closed sheaf-category internal Hom into the unit. -/
abbrev dual (L : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  (ihom L).obj (𝟙_ _)

/-- An etale sheaf placed in the stated shifted degree in the ordinary derived category. -/
abbrev etaleSingle (L : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) (m : ℤ) :=
  ((DerivedCategory.singleFunctor _ 0).obj L)⟦m⟧

/-- The specified ordinary evaluation, sending a local basis and its dual to one. -/
def pairing (L : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    L ⊗ dual A T L ⟶ 𝟙_ _ :=
  (ihom.ev L).app (𝟙_ _)

/-- The two factors: false is the line, true is its internal sheaf dual. -/
def factor (L : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) (b : Bool) :
    Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) :=
  if b then dual A T L else L

end AlgebraicGeometry.ShiftedLineSiteInverse
