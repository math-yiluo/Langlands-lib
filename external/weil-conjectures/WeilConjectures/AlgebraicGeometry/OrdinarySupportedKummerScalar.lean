/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.OrdinarySupportedKummerBoundary
public import WeilConjectures.CategoryTheory.ExactDegreeZero

/-!
# Derived coefficient change of supported Kummer classes

Source: Stacks Project, Tag 07A6; blueprint
sec-smooth-purity/sk-prop-sf-cbc/lem-amb-cartier-kummer-map.md, final paragraph
(auxiliary; not a blueprint node).

## Main definitions

* `SupportedDerivedScalarUnit`: the derived scalar-unit universal property.
* `SupportedKummerScalar`: the normalized scalar-extension square for the classes.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local instance 10000] SheafExactDegreeZero.scalarWeakSheafify

/-- The universal-property formulation of a derived scalar-extension unit at F.
The target is G in degree zero, while test objects K range over the entire unbounded
derived category. This is derived tensor extension, with no flatness assumption on S.
Source: Stacks 07A6 (auxiliary; not a blueprint node). -/
@[irreducible]
def SupportedDerivedScalarUnit {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (φ : R →+* S) (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R))
    (G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} S))
    (η : F ⟶ (Sheaf.restrictScalars T.smallEtaleTopology φ).obj G) : Prop :=
  SheafExactDegreeZero.scalarUniversal T.smallEtaleTopology φ F G η

end AlgebraicGeometry.Etale
