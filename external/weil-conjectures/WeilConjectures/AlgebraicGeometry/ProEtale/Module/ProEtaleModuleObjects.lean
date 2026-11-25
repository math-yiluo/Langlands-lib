/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.SheafTensorStructure
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic

/-!
# Sheaves of pulled-back condensed-ring modules

The coefficient ring on a scheme's small pro-etale site is the canonical ring object
provided by `AlgebraicGeometry.ProEtale.coefficientRing`.  The module category is
Mathlib's category of module objects for that ring object in the sheaf category.

## Implementation details

`condensedModuleCategory` is an `abbrev` for `CategoryTheory.Mod`, so that its instances
(the faithful forgetful functor, the regular module, ...) apply directly.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

/--
For a scheme `X` and a condensed ring object `Λ`, this is the category
`Mod_{Λ_X}(Sh(X_proet, Ab))` of sheaves of modules over the pulled-back coefficient
ring `Λ_X := p_X^* Λ`.  Its objects are abelian sheaves equipped with an action
`Λ_X ⊗ M ⟶ M` satisfying the unit and associativity axioms.
-/
noncomputable abbrev condensedModuleCategory (X : Scheme.{u})
    (Λ : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})) : Type _ :=
  let R := AlgebraicGeometry.ProEtale.coefficientRing X Λ
  letI : MonObj R.X := R.mon
  CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R.X

end AlgebraicGeometry.ProEtale
