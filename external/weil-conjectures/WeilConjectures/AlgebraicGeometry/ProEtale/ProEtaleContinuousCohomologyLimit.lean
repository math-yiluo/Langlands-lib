/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.AlgebraicGeometry.ProEtaleMilnorEpimorphic
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleProductsDerived

/-!
# Derived sections of epimorphic inverse limits on the pro-etale site

Abelian sheaves are represented by modules over the constant integer ring sheaf.
The abbreviations below specialize the recorded constant-sheaf, module-sheaf and
K-injective derived-sections constructions. No coefficient action is supplied as
an additional hypothesis: the integer action on an abelian sheaf is unique.

## References

* Bhatt--Scholze, Propositions 3.1.9 and 3.1.10
-/

@[expose] public section

set_option autoImplicit false

universe t w w'

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- The constant integer ring sheaf on the unchanged small pro-etale site. -/
noncomputable abbrev continuousCohomologyIntegerSheaf (X : Scheme.{t}) :=
  (constantSheaf (Scheme.ProEt.topology X) CommRingCat.{t + 1}).obj
    (CommRingCat.of (ULift.{t + 1} ℤ))

/-- Abelian sheaves, presented as modules over the constant integer sheaf.
The integer action on any abelian sheaf extends uniquely to locally constant integer
sections, so this imposes no additional structure on the abelian sheaves of the statement. -/
noncomputable abbrev continuousCohomologyAbelianSheaves (X : Scheme.{t}) :=
  ringedSiteModules.{t + 1}
    ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj
        (continuousCohomologyIntegerSheaf X))


end AlgebraicGeometry.ProEtale
