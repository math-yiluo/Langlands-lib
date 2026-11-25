/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.ConstantCoefficientScalarExtension
public import WeilConjectures.ConstructibleSheaf.Defs

/-! # Local constant finite-module descriptions on a site

Source: Stacks Project, sites-cohomology.tex, Tags 094H and 094I
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u

open CategoryTheory

namespace SheafOfModules

/-- Local trivializations by constant sheaves of finitely generated coefficient modules.
The module may vary with the member of the covering sieve; no points are used.
Source: Stacks Project, Tags 094H and 094I
(auxiliary; not a blueprint node). -/
def IsLocallyConstantFiniteTypeModules {C : Type u} [Category.{u} C]
    (J : GrothendieckTopology C) (B : Type u) [CommRing B]
    (F : SheafOfModules.{u} (constantCoefficientRing J B)) : Prop :=
  ∀ V : C, ∃ S : Sieve V, S ∈ J V ∧
    ∀ (U : C) (f : U ⟶ V), S f →
      ∃ M : ModuleCat.{u} B, Module.Finite B M ∧
        Nonempty (F.over U ≅ ((constantCoefficientModule J B).obj M).over U)

end SheafOfModules
