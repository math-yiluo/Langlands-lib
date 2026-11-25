/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.Scalar.ScalarExtensionFunctor
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImageComparison

import all WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryRestrictionPullbackSquare
import all WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenScalarCocycle
import WeilConjectures.AlgebraicGeometry.Scalar.ScalarAssociatorConjugate
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Coefficient cocycle for the ambient direct-image mate

## References

* Stacks Tags 07A7 and 0E47
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Functor
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] directImageConstantAdjunction
  proEtaleRingDerivedAdjunction proEtaleConstantRingComparison proEtaleRingModulePullback
  completedAdicDerivedChange reductionDerivedChange
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
  scalarExtensionFunctor_composition

end AlgebraicGeometry.ProEtale
