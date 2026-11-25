/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ConstructibleSheaf.OpenClosedStratification
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZeroAdjunction
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZeroExact
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicFiniteOperations
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective

import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Proper
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
# The clopen component description for a section of an open immersion

Source: blueprint main-20261015, sec-proetale-coefficients/sk-def-sf-operations,
lem-weil-pbc-clopen-section-direct-image.proof.md, disjoint-open-cover description
and displayed section formula; Stacks Project, `proetale.tex`, Tags 098K and 09AE
(blueprint: lem-sp-clopen-section-component).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
attribute [local instance] preservesBinaryBiproduct_of_preservesBiproduct
section Generic

universe v

variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
  [Preadditive C] [Preadditive D] [Preadditive E]
  [HasBinaryBiproducts C]

end Generic

section Generic

universe v

variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
  [Preadditive C] [Preadditive D] [Preadditive E]
end Generic

end AlgebraicGeometry.Scheme
