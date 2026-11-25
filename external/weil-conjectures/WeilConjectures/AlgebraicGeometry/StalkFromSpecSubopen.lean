/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Stalk

/-! # Compatibility of canonical stalk maps with nested open inclusions

Source: Mathlib AlgebraicGeometry/Stalk.lean, Opens.fromSpecStalkOfMem_ι.
(blueprint: lem-pc-stalk-from-spec-subopen)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Opens

/-- Canonical maps from the ambient stalk spectrum commute with nested inclusions.

Source: Mathlib AlgebraicGeometry/Stalk.lean, Opens.fromSpecStalkOfMem_ι (line 176).
Proof: Compose both sides with V.ι. By associativity and homOfLE_ι, the left
side becomes U.fromSpecStalkOfMem followed by U.ι. Both sides are therefore
Y.fromSpecStalk y by fromSpecStalkOfMem_ι. Cancel the monomorphism V.ι.
This includes U=V, V=Y, and every non-affine open neighbourhood.
(blueprint: lem-pc-stalk-from-spec-subopen) -/
theorem fromSpecStalkOfMem_homOfLE {Y : Scheme.{u}}
    (y : Y) (V : Y.Opens) (hyV : y ∈ V) (U : Y.Opens) (hUV : U ≤ V) (hyU : y ∈ U) :
    U.fromSpecStalkOfMem y hyU ≫ Y.homOfLE hUV = V.fromSpecStalkOfMem y hyV := by
  apply (cancel_mono V.ι).1
  simp only [Category.assoc, Scheme.homOfLE_ι, Scheme.Opens.fromSpecStalkOfMem_ι]

end AlgebraicGeometry.Scheme.Opens
