/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.OpenScalarTensor.OpenScalarTensorData
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingPullbackComparison
import all WeilConjectures.Algebra.Homology.ScalarPullback.KFlatScalarComparisonNormalization
import all WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryRestrictionPullbackSquare
import all WeilConjectures.AlgebraicGeometry.ProEtale.Derived.ProEtaleDerivedPullbackCoherence
import all WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalDerivedPullbackNormalization

set_option linter.privateModule false

/-! # Geometric composition of the scalar/pullback comparison

## References

* Stacks Project, Tag 0D6D
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
attribute [local instance 100000] proEtaleRingModules_hasDerivedCategory
attribute [local instance 200000] SheafOfModules.instAbelian
namespace AlgebraicGeometry.ProEtale.OpenScalarTensor

end AlgebraicGeometry.ProEtale.OpenScalarTensor
