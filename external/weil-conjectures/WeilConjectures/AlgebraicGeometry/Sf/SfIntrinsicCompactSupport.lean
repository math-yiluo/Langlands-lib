/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZeroExact
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
public import WeilConjectures.Compactification.Defs

/-!
# Compact-support candidate in the intrinsic constant-ring presentation

This is the same compactification formula, using the canonical realization
of module-valued sheaves as modules over the constant ring sheaf. Compactification
independence remains confined to the separately specified etale-origin subcategory.

## References

* Stacks, Tags 03DI and 03DA
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The candidate attached to the specified compactification `c = (j, g)` is the
termwise exact extension by zero followed by the K-injective total right-derived
image of `g`, on all unbounded complexes. This is precisely `Rg_* j_!`, expressed
in the intrinsic constant-ring presentation, with no assertion of unbounded
compactification independence. -/
noncomputable def sfIntrinsicCompactSupport {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (A : Type u) [CommRing A] [Finite A] :
    proEtaleDerivedCategory X A ⥤ proEtaleDerivedCategory Y A :=
  (sfIntrinsicExtensionByZero c.i A).mapDerivedCategory ⋙
    proEtaleConstantDerivedDirectImage c.g A

end AlgebraicGeometry.Scheme
