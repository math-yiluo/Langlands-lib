/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZero
public import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# The open extension adjunction in intrinsic constant coefficients

The canonical coefficient realization transports the sectionwise restriction and
its extension-by-zero adjunction to the intrinsic coefficient presentation.

## References

* Stacks, Tags 03DI, 03CY and 09AE
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Restriction to the open subscheme in intrinsic constant coefficients. Before
canonical coefficient realization its value at `V → U` is the original module at
`V → U → X`, with the same restrictions and scalar action. The realization inverse
only restricts scalars to constants, and realization extends them uniquely to locally
constant sections. Thus this is the usual restriction, in the presentation used by
`sfIntrinsicExtensionByZero`, without an arbitrary coefficient identification. -/
noncomputable def sfIntrinsicOpenRestriction {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (A : Type u) [CommRing A] [Finite A] :
    proEtaleRingModules X (proEtaleConstantRing X A) ⥤
      proEtaleRingModules U (proEtaleConstantRing U A) :=
  (sfIntrinsicModuleEquivalence X A).inverse ⋙
    ProEtale.openImmersionRestriction (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j ⋙
      (sfIntrinsicModuleEquivalence U A).functor

/-- The canonical extension-by-zero adjunction for intrinsic constant coefficients: the
fixed-scalar extension-by-zero adjunction composed with the coefficient realization
equivalences. -/
noncomputable def sfIntrinsicExtensionByZeroAdjunction {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (A : Type u) [CommRing A] [Finite A] :
    sfIntrinsicExtensionByZero j A ⊣ sfIntrinsicOpenRestriction j A :=
  ((sfIntrinsicModuleEquivalence U A).symm.toAdjunction.comp
    (ProEtale.openImmersionLowerShriekAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j)).comp
        (sfIntrinsicModuleEquivalence X A).toAdjunction

end AlgebraicGeometry.Scheme
