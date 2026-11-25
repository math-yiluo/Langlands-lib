/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.PullbackTensorCanonical.PullbackTensorCanonicalShiftUnit
public import WeilConjectures.Algebra.Homology.DerivedTensorConstraints.DerivedTensorAdditiveConstraints
public import WeilConjectures.Algebra.Homology.Ringed.RingedTopoiDerivedPullbackIndependentSupplement
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Algebra.Homology.KFlatTotalTensorModel.KFlatTotalTensorModelSupplement
import all WeilConjectures.Algebra.Homology.PullbackTensorCanonical.PullbackTensorCanonicalShiftUnit
import all WeilConjectures.Algebra.Homology.DerivedTensorConstraints.DerivedTensorAdditiveConstraints
import WeilConjectures.SecSmoothPurity.CochainComparisonMonoidalEquationsSupplement
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived

/-! # Transport and signed coherence of a normalized resolving tensor comparison

Source: Stacks Project, sites-cohomology.tex, Tags 07A4, 06YU and 0FPT;
more-algebra.tex, section-sign-rules, item-shift-tensor and item-flip-tensor-product.
(blueprint: lem-pur-resolving-tensor-signed-coherence).

All tensors and representative comparisons are the published K-flat constructions.
The sole construction below conjugates the specified natural isomorphism by eta.
In the shift equation the first shift is extracted before the second: the second
shift therefore uses the original first-factor degree, as in the source node.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe uC vC uD vD r wR wS

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.CochainPullback hiding Modules
open SheafOfModules.KFlatFixedTensor
open SheafOfModules.PullbackTensorCanonical

namespace SheafOfModules.ResolvingTensorSigned

attribute [local irreducible] SheafOfModules.monoidalCategory
  siteDerivedTensorIndependentCoefficients representativeIso
  CategoryTheory.Functor.mapDerivedCategory
  PullbackTensorCanonical.IsNormalized HasCanonicalTensorShifts
  DerivedTensorConstraints.IsNormalized

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C]
  {D : Type uD} [Category.{vD} D] [EssentiallySmall.{r} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {R : Sheaf J CommRingCat.{r}} {S : Sheaf K CommRingCat.{r}}
  [HasDerivedCategory.{wR} (Modules R)] [HasDerivedCategory.{wS} (Modules S)]
  (f : RingedPullback.{r, uC, vC, uD, vD} R S)
  [PreservesFiniteLimits f.L] [PreservesFiniteColimits f.L]
  (L : DerivedCategory (Modules R) ⥤ DerivedCategory (Modules S))

variable (k : Comparison.{r, uC, vC, uD, vD} f)
  (epsilon : DerivedCategory.Q ⋙ L ⟶ pull.{r, uC, vC, uD, vD} f ⋙ DerivedCategory.Q)
  [L.CommShift ℤ] [NatTrans.CommShift epsilon ℤ]
  [(derivedTensor R).CommShift₂Int] [(derivedTensor S).CommShift₂Int]

end SheafOfModules.ResolvingTensorSigned
