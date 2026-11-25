module

import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Properties

public import StacksFrontier.RingTheory.Nagata.Defs

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Japanese and Nagata schemes

A scheme is *Japanese* (when integral) or *Nagata* when every point has an affine
open neighbourhood whose ring of sections is a Japanese, resp. Nagata, ring.

## Main definitions

* `IsJapaneseScheme`, `IsNagataScheme`.
-/

@[expose] public section

open AlgebraicGeometry

universe u

/-- A scheme `X` is **Nagata** if every point has an affine open neighbourhood `U` whose ring of
sections `O_X(U)` is a Nagata ring. -/
def IsNagataScheme (X : Scheme.{u}) : Prop :=
  ∀ x : X, ∃ U : X.affineOpens, x ∈ U.val ∧ StacksIsNagataRing Γ(X, U.val)
