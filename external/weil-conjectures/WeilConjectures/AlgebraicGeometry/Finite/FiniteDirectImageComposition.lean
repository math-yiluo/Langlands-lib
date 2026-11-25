/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp

/-!
# Canonical finite-level composition of derived direct images

Source: Weil blueprint, sec-smooth-purity/sk-def-sf-operations, order 1470, clause (1);
Stacks Tag 0D6E (blueprint: lem-weil-derived-direct-image-composition).

This is the specialization used by refinement comparisons. It derives the actual
fibre-product-pasting map, with the universal right-derived unit normalization.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

/-- At finite level, the canonical compositor on the entire unbounded derived category.
The exact inverse-image adjunction makes the first direct image preserve K-injectives.
The generic universal-property compositor is applied to the underived fibre-product
pasting isomorphism, and inverted to have the source's orientation.
Source: blueprint order 1470, clause (1), finite-level proof; Stacks Tag 0D6E
(blueprint: lem-weil-derived-direct-image-composition). -/
def finiteDirectImageComposition (Λ : Type (u + 1)) [CommRing Λ]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (lowerStar (ModuleCat.{u + 1} Λ) (f ≫ g)).rightDerivedFunctor ≅
      (lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor ⋙
        (lowerStar (ModuleCat.{u + 1} Λ) g).rightDerivedFunctor :=
  letI := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).preservesKInjectiveComplexes
  (Functor.rightDerivedFunctorCompIso'
    (lowerStar (ModuleCat.{u + 1} Λ) f) (lowerStar (ModuleCat.{u + 1} Λ) g)
    (lowerStarComp (ModuleCat.{u + 1} Λ) f g)).symm

end AlgebraicGeometry.ProEtale
