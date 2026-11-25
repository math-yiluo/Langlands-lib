/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.AlgebraicGeometry.Scheme

/-! # Invertibility of a natural number after pullback

Source: the global-functions map in the universal-base argument of the finite P1 check.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A natural number invertible on the base is invertible on its inverse image.
Source: blueprint lem-sp-tower-p1-arbitrary-base-integrals, steps 1 and 3.
(auxiliary; not a blueprint node)
Proof: map the given unit by the global-sections ring homomorphism. Its value on
N is N by map_natCast. Transport the resulting IsUnit proof along that equality. -/
theorem finiteP1_unitOnPullback (N : ℕ) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hY : IsUnit (N : Γ(Y, ⊤))) : IsUnit (N : Γ(X, ⊤)) := by
  exact (map_natCast f.appTop.hom N) ▸ hY.map f.appTop.hom

end AlgebraicGeometry
