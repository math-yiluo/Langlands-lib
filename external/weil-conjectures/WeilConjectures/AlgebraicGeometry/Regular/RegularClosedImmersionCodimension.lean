/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.Regular.RegularSequence

/-!
# Regular closed immersions with varying codimension

## References

* Stacks Project, Divisors, regular ideal sheaves and regular immersions, Tags 063D, 063G and 063J
* Stacks Project, Divisors, Tags 063D, 063G and 063J
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A closed immersion has codimension function `c` when, around every source point `y`,
its ideal has regular equations of length `c y` on an ambient affine neighbourhood.
The kernel on sections is the defining ideal of the closed subscheme on that affine.
The condition is imposed along the source, so it includes open-and-closed immersions of
codimension zero and empty sources. No constancy or rank theorem is built into the data. -/
def IsRegularClosedImmersionWithCodimension {Y X : Scheme.{u}}
    (i : Y ⟶ X) (c : Y → ℕ) : Prop :=
  IsClosedImmersion i ∧ ∀ y : Y, ∃ U : X.affineOpens, i y ∈ U.1 ∧
    ∃ a : List Γ(X, U.1), a.length = c y ∧
      RingTheory.Sequence.IsRegular Γ(X, U.1) a ∧
      Ideal.ofList a = RingHom.ker (i.app U.1).hom

end AlgebraicGeometry
