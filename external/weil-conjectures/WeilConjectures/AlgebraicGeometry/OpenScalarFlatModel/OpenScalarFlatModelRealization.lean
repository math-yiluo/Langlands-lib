/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantExact
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Flat
import WeilConjectures.CategoryTheory.Constant.ConstantScalarRestrictionTensorSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantExact

/-! # Flatness of finite constant-coefficient realization

## References

* Stacks Project, Tags 03CY and 03DA
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory
namespace AlgebraicGeometry.ProEtale.OpenScalarFlatModel

end AlgebraicGeometry.ProEtale.OpenScalarFlatModel
