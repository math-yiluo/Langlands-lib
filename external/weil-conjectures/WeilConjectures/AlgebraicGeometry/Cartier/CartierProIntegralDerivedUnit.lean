/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionDataSupplement
import all WeilConjectures.AlgebraicGeometry.EtaleSupportedIntegralDerivedUnit
import all Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.AlgebraicGeometry.ExactFunctorDerivedUnit
import all WeilConjectures.AlgebraicGeometry.ResidueQuotientDerivedUnit
import all WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
import all Mathlib.Algebra.Homology.ShortComplex.ShortExact
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Data.ZMod.Basic
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Whiskering
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Reduction
import all WeilConjectures.Algebra.Homology.DivisibleReduction.DivisibleExtensionDerivedReductionSupplement
import all WeilConjectures.Mathlib.Algebra.Category.Grp.ZModuleEquivalence
import all WeilConjectures.SixFunctors.BaseChange.DerivedForget
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Coinduce
import all Mathlib.CategoryTheory.Abelian.ShortExact
import all WeilConjectures.AlgebraicGeometry.SupportedKummerScalarSource
import all WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerScalarSupplement
import all WeilConjectures.AlgebraicGeometry.SupportedKummerScalarMaps
import all WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerBoundarySupplement
import all WeilConjectures.SixFunctors.BaseChange.RestrictScalars
import all WeilConjectures.AlgebraicGeometry.SupportedKummerScalarDerived
import all WeilConjectures.CategoryTheory.FlatScalarUnit
import all WeilConjectures.CategoryTheory.Exact.ExactDegreeZeroSupplement
import all WeilConjectures.CategoryTheory.ExactRightDerivedAdjointKFlatRepresentative
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
import all WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import all Mathlib.CategoryTheory.Adjunction.Unique
import all Mathlib.CategoryTheory.Functor.Derived.Adjunction
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import all WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic
import all WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import all Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape
import all WeilConjectures.AlgebraicGeometry.FiniteOrdinaryScalarUnit
import all Mathlib.AlgebraicGeometry.Morphisms.Finite
import all WeilConjectures.SixFunctors.Finite.Stalk
import all Mathlib.CategoryTheory.Sites.Adjunction
import all WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import all WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
import all Mathlib.Algebra.Category.ModuleCat.Products
import all WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars
import all WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import all WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import all Mathlib.AlgebraicGeometry.Scheme
import all WeilConjectures.AlgebraicGeometry.ScalarUniversalDerivedUnit
import all WeilConjectures.AlgebraicGeometry.SupportedIntegralResidueSequence
import all WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import all WeilConjectures.SixFunctors.Finite.Exact
import all Mathlib.Algebra.Homology.ShortComplex.Ab
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.AlgebraicGeometry.Cartier.CartierProIntegralResidueDerivedUnit
import WeilConjectures.AlgebraicGeometry.Cartier.CartierProIntegralScalar
import WeilConjectures.CategoryTheory.DerivedUnit.DerivedScalarExtUnitZero

/-! # Cartier reduction and site comparison
Source: blueprint main-20261015, Cartier comparison proof
(blueprint: lem-sp-cartier-reduction-site-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
attribute [local instance] AlgebraicGeometry.cartierEtaleAbSheafify
  WeilConjectures.sfAbSheafify AlgebraicGeometry.cartierEtaleModuleSheafify
  AlgebraicGeometry.cartierProModuleSheafify AlgebraicGeometry.cartierEtaleAbHasExt
  AlgebraicGeometry.ProEtale.geoCartierIntegralExt AlgebraicGeometry.Etale.hasExt_sheaf_moduleCat
  AlgebraicGeometry.ProEtale.geoCartierModuleExt
namespace AlgebraicGeometry.ProEtale
attribute [local irreducible] comparisonUpperStar cartierUnitsComparison
  cartierRootsComparison cartierRootsIso cartierEtaleKummerUnit cartierProKummerUnit
  cartierProIntegralGenerator cartierProRootMap cartierReducedEtale cartierReducedPro
  CartierEtaleReductionSpec CartierProReductionSpec cartierResidueReducedPro

/-- Let n>0, R=ULift(Z/n), A a commutative ring killed by n, i:D→Z a closed immersion and φ:R→A. If
Cartier classes cR,cA satisfy GeoCartierScalarCompatibility [lemma-cycle-class-cartier-divisor],
then the pro-etale supported integral generator i_*Z_D→forget(i_*A_D) is a degree-zero unbounded
scalar unit [def-sfb-cartier-reduction-data, def-sp-derived-scalar-ext-unit].
Source: blueprint Cartier derived reduction and comparison paragraphs; Stacks 0152,
06YY and 0GLZ (blueprint: lem-sp-cartier-pro-integral-derived-unit).
Proof: Use the supported pro-etale residue quotient unit. Extract from coefficient compatibility the
derived unit on supported constants for extension R→A. Compose the ordinary derived-unit Hom
bijections. Composite coefficient forgetting is definitionally direct forgetting. The normalized
supported integral scalar identity identifies the composite map with the stated integral generator.
Finally the zero-shift comparison identifies its ordinary unit property with the degree-zero
Ext-unit property. -/
theorem pro_integral_derived_unit
    (A : Type (u + 1)) [CommRing A] (n : ℕ) (hn : 0 < n)
    (hA : (n : A) = 0) (hR : (n : ULift.{u + 1} (ZMod n)) = 0)
    {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i]
    (φ : ULift.{u + 1} (ZMod n) →+* A)
    (cR : GeoCartierClass (ULift.{u + 1} (ZMod n)) n hR i)
    (cA : GeoCartierClass A n hA i)
    (hcompat : GeoCartierScalarCompatibility φ n hR hA i cR cA) :
    CartierScalarUnit (cartierForget A Z)
      ((lowerStar AddCommGrpCat.{u + 1} i).obj
        ((constantSheaf (Scheme.ProEt.topology D) AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))))
      ((lowerStar (ModuleCat.{u + 1} A) i).obj (geoCartierConstant A D)) 0
      (Ext.mk₀.{u + 1} (cartierProIntegralGenerator A i)) := by
  let R := ULift.{u + 1} (ZMod n)
  unfold GeoCartierScalarCompatibility at hcompat
  obtain ⟨η, θ, hη, hθ, hηunit, hθunit, hsquare⟩ := hcompat
  let U := Sheaf.restrictScalars (Scheme.ProEt.topology Z) φ
  let V := cartierForget R Z
  let F := (lowerStar AddCommGrpCat.{u + 1} i).obj
    ((constantSheaf (Scheme.ProEt.topology D) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
  let G := (lowerStar (ModuleCat.{u + 1} R) i).obj (geoCartierConstant R D)
  let H := (lowerStar (ModuleCat.{u + 1} A) i).obj (geoCartierConstant A D)
  let η' : G ⟶ U.obj H := (lowerStar (ModuleCat.{u + 1} R) i).map η
  have hRu := pro_integral_residue_derived_unit n hn i
  unfold GeoCartierScalarUnit at hηunit
  have hηunit' : U.DerivedUnit G H η' := by
    simpa only [Functor.DerivedUnit, Sheaf.IsDerivedBaseChange,
      Sheaf.derivedRestrictScalars, Category.assoc] using hηunit
  have hcomp := Functor.scalar_unit_comp U V F G H
    (cartierProIntegralGenerator R i) η'
    hRu hηunit'
  have hγ := pro_supported_generator_scalar φ i η hη
  change (cartierForget A Z).DerivedUnit F H
    (cartierProIntegralGenerator R i ≫ V.map η') at hcomp
  rw [hγ] at hcomp
  exact hcomp.extUnit_zero
end AlgebraicGeometry.ProEtale
