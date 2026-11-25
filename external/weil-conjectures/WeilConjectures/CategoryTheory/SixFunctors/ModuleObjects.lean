/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic

/-!
# Module objects in a monoidal category

Source: blueprint main-20261015, sec-proetale-coefficients/sk-def-sfb-module-objects
(blueprint: sk-def-sfb-module-objects).

For a monoid object `R` in a monoidal category `C`, `CategoryTheory.Mod C R` is
Mathlib's category of left `R`-module objects.  Its objects carry an action
`R ⊗ M ⟶ M` with the unit and associativity laws, and its morphisms are the
maps commuting with the actions.  The regular module is supplied by
`CategoryTheory.Mod.regular`.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory

namespace CategoryTheory

/-- The category of left module objects over a monoid object.

Source: blueprint sk-def-sfb-module-objects, clauses 1--3
(blueprint: sk-def-sfb-module-objects). -/
abbrev moduleObjects (C : Type u) [Category.{v, u} C] [MonoidalCategory C]
    (R : Mon C) : Type (max u v) :=
  Mod C R.X

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

open AlgebraicGeometry Scheme

/-- The sheaf category of modules over the pulled-back condensed ring `Λ_X`.

Source: blueprint sk-def-sfb-module-objects, clause 3
(blueprint: sk-def-sfb-module-objects). -/
abbrev pulledBackModuleObjects
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :=
  moduleObjects (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (coefficientRing X (Mon.mk Λ))

end AlgebraicGeometry.ProEtale
