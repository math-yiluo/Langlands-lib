/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.Ideal.Operations
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible

/-! # Ample invertible modules on schemes

Source: Stacks Project, Properties, Section 01PR and Definition 01PS
(blueprint: def-weil-pbc-ample-invertible-module).
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

universe u

/-- The non-vanishing locus `X_s` of a global section `s` of a module `M`: the points `x`
where the germ of `s` is outside the maximal ideal times the stalk module, equivalently
where `s` has nonzero value in the fibre `M_x ⊗ κ(x)`. This is exactly the predicate used
inline in `IsAmple`.
Source: Stacks Project, Properties, Section 01PR
(blueprint: def-weil-pbc-ample-invertible-module).
-/
def nonvanishingLocus {X : Scheme.{u}} (M : X.Modules)
    (s : M.val.presheaf.obj (Opposite.op ⊤)) : Set X :=
  {y | (TopCat.Presheaf.germ M.val.presheaf ⊤ y trivial) s ∉
    (IsLocalRing.maximalIdeal (X.presheaf.stalk y)) •
      (⊤ : Submodule (X.presheaf.stalk y) ↑(TopCat.Presheaf.stalk M.val.presheaf y))}

/-- The absolute ampleness condition of Stacks Properties Definition 01PS.
The open `U` is exactly the locus where the germ is outside the maximal ideal times
the stalk module, equivalently where the section has nonzero residue-field value.
Source: Stacks Project, Properties, Definition 01PS
(blueprint: def-weil-pbc-ample-invertible-module).
-/
def IsAmple (X : Scheme.{u}) (L : X.Modules) [L.IsInvertible] : Prop :=
  CompactSpace X ∧ ∀ x : X, ∃ n : ℕ, 0 < n ∧
    ∃ s : (L.tensorPow n).val.presheaf.obj (Opposite.op ⊤), ∃ U : X.Opens,
      x ∈ U ∧ IsAffineOpen U ∧ ∀ y : X, y ∈ U ↔
        (TopCat.Presheaf.germ (L.tensorPow n).val.presheaf ⊤ y trivial) s ∉
          (IsLocalRing.maximalIdeal (X.presheaf.stalk y)) •
            (⊤ : Submodule (X.presheaf.stalk y)
              ↑(TopCat.Presheaf.stalk (L.tensorPow n).val.presheaf y))

/-- Sanity check: the predicate in `IsAmple` is `nonvanishingLocus` by definition. -/
example {X : Scheme.{u}} (M : X.Modules) (s : M.val.presheaf.obj (Opposite.op ⊤)) (y : X) :
    y ∈ nonvanishingLocus M s ↔
      (TopCat.Presheaf.germ M.val.presheaf ⊤ y trivial) s ∉
        (IsLocalRing.maximalIdeal (X.presheaf.stalk y)) •
          (⊤ : Submodule (X.presheaf.stalk y) ↑(TopCat.Presheaf.stalk M.val.presheaf y)) :=
  Iff.rfl

end AlgebraicGeometry.Scheme.Modules
