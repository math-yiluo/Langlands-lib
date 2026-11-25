/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# Cohomological support on the small pro-etale site
-/

@[expose] public section

universe t

namespace AlgebraicGeometry.Scheme

/-- The cohomological support of a complex of sheaves of `A`-modules on the small
pro-etale site of `Y` is the set of integers where its cohomology sheaf is nonzero.
The complex is viewed in `proEtaleDerivedCategory Y A`; cohomology depends only on
its quasi-isomorphism class. Here nonzero means not a zero object of the category
of sheaves of modules, rather than inequality with a chosen zero object. -/
def proEtaleCohomologicalSupport {Y : Scheme.{t}} {A : Type t} [CommRing A]
    (K : proEtaleDerivedCategory Y A) : Set ℤ :=
  {r | ¬ CategoryTheory.Limits.IsZero
    ((@DerivedCategory.homologyFunctor _ _ _ (HasDerivedCategory.standard _) r).obj K)}

end AlgebraicGeometry.Scheme
