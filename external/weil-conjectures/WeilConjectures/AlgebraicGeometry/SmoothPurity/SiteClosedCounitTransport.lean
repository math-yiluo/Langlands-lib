/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FixedComparisonDirectImageMate
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonClassAdjunction
public import WeilConjectures.SixFunctors.ProEtale.FullCohomologicalDimension
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleUpperShriek
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Constructible
public import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
public import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekIndependence
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalCompactSupportSiteComparison
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

set_option linter.privateModule false

/-!
# Counit normalization of the site-transported closed adjoint

Source: literature/blueprint/master/blueprint/sec-six-functors/sk-prop-sf-biduality-general/
lem-coef-finite-dualizing.md, closed-immersion calculation (*); the normalized Hom chain in
literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-sf-existence/
thm-sf-ambient-adjoint-class.proof.md
(blueprint: lem-coef-site-closed-counit-transport).

We retain the identity-open compactification in the notation. Its ordinary adjunction is
identified with the closed direct-image adjunction by the canonical identity-open
normalization, and the inverse compact-support comparison is the direct-image mate delta.
Thus the formula below is (*) with these canonical identifications displayed by the
compactification interface, rather than a separately chosen Hom equivalence.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

private theorem inclusion_comp_inv
    {B C D : Type*} [Category* B] [Category* C] [Category* D]
    [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory B] [HasDerivedCategory C] [HasDerivedCategory D]
    (V : B ⥤ C) (W : C ⥤ D) [V.Additive] [W.Additive]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    [PreservesFiniteLimits W] [PreservesFiniteColimits W]
    (K : DerivedCategory.Plus B) :
    DerivedCategory.Plus.ι.map ((Functor.mapDerivedCategoryPlusCompIso V W).inv.app K) =
      (Functor.mapDerivedCategoryCompIso V W).hom.app K.obj := by
  exact congrArg Iso.inv (show DerivedCategory.Plus.ι.mapIso
    ((Functor.mapDerivedCategoryPlusCompIso V W).app K) =
    (Functor.mapDerivedCategoryCompIso V W).symm.app K.obj from
    Iso.ext (Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app V W K))

end AlgebraicGeometry.ProEtale
