/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedModuleConstructible
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars
public import WeilConjectures.AlgebraicGeometry.ProEtale.Extension.ProEtaleExtensionZeroComparison
public import WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf
import WeilConjectures.AlgebraicGeometry.ProEtaleLisseFiniteModelsFromLisse
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleFixedModuleLocalConstancy
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheaf
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.AlgebraicGeometry.ProEtaleGeometricStalk
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelStalks
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Point.Over
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelLocalConstancy
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence
import Mathlib.CategoryTheory.Functor.TypeValuedFlat
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison

/-! # Supported constructible origin and unbounded coefficient comparison

Source: Stacks Project, Tags 09AK, 09AL, 09AF, 07A4 and 03DJ
(blueprint: lem-sp-supported-constructible-origin-comparison).

All functors use the fixed-scalar presentation of constant-ring module sheaves.
Intrinsic constructibility is the recorded fixed-module predicate, not an etale-origin
predicate. The coefficient B is the constant sheaf on B with its A-action via the
specified ring homomorphism. All derived categories are ordinary and unbounded.
The definitions construct the canonical isomorphisms for every chosen origin; the theorem
asserts existence of a bounded constructible origin and boundedness of its open extensions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor MonoidalCategory
namespace AlgebraicGeometry.ProEtale
namespace SupportedConstructibleOriginComparison

/-- Pullback of constant module sheaves, uniquely normalized by the adjunction on
terminal sections. Hence each pulled-back constant section is sent to itself.
Source: Stacks 0H7J and 099R
(blueprint: lem-sp-supported-constructible-origin-comparison). -/
@[irreducible] def constantModuleComparison (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) ⋙
      comparisonUpperStar (ModuleCat.{u + 1} A) T ≅
        constantSheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A) :=
  comparisonUpperStarConstantSheafIso A T

/-- The degree-zero coefficient comparison. Restriction of scalars gives B exactly
its A-action through f; the constant comparison preserves every b in B.
Source: Stacks 0H7J and 07A4
(blueprint: lem-sp-supported-constructible-origin-comparison). -/
@[irreducible] def coefficientComparison {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (f : A →+* B) (T : Scheme.{u}) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj
      ((_root_.DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
          ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B)))) ≅
    (_root_.DerivedCategory.singleFunctor _ 0).obj
      ((constantSheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)).obj
        ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B))) :=
  ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (_root_.DerivedCategory.singleFunctor _ 0).mapIso
      ((constantModuleComparison T A).app
        ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B)))

/-- The canonical c_e: descend the natural sheaf comparison termwise, then apply
pro-etale extension by zero to the specified e. These are the fixed-module coordinates
of the recorded intrinsic extension by zero.
Source: Stacks 09AF and 03DJ
(blueprint: lem-sp-supported-constructible-origin-comparison). -/
@[irreducible] def openComparison (A : Type (u + 1)) [CommRing A]
    {U Z : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j]
    (L : Etale.DerivedCategoryModule A U)
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} A)))
    (e : (comparisonUpperStar (ModuleCat.{u + 1} A) U).mapDerivedCategory.obj L ≅ M) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory.obj
      ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj L) ≅
    (ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj M :=
  (Functor.mapDerivedCategorySquareIso
      (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} A) j)).app L ≪≫
    (ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.mapIso e

/-- The canonical t_e in the unbounded derived category: derived tensor pullback,
then 1 tensor beta_B, then c_e tensor 1. No Tor bound is used.
Source: Stacks 07A4, 09AF and 0H7J
(blueprint: lem-sp-supported-constructible-origin-comparison). -/
@[irreducible] def tensorComparison
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (f : A →+* B) {U Z : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j]
    (L : Etale.DerivedCategoryModule A U)
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} A)))
    (e : (comparisonUpperStar (ModuleCat.{u + 1} A) U).mapDerivedCategory.obj L ≅ M) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory.obj
      (((Etale.derivedTensor (ModuleCat.{u + 1} A) Z).obj
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj L)).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj
            ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
              ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B))))) ≅
    ((ProEtale.derivedTensor (ModuleCat.{u + 1} A) Z).obj
      ((ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj M)).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A)).obj
            ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B)))) :=
  (derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso (ModuleCat.{u + 1} A)
      ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj L)).app
        ((_root_.DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
            ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B)))) ≪≫
    (((ProEtale.derivedTensor (ModuleCat.{u + 1} A) Z).obj
      ((comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory.obj
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj L))).mapIso
          (coefficientComparison f Z)) ≪≫
    ((ProEtale.derivedTensor (ModuleCat.{u + 1} A) Z).mapIso (openComparison A j L M e)).app _

end SupportedConstructibleOriginComparison
end AlgebraicGeometry.ProEtale
