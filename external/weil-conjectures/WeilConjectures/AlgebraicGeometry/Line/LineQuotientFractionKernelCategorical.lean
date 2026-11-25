/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Categorical sectionwise zero criterion -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules

/-- A composite of module-sheaf morphisms is zero exactly when it vanishes on every section. -/
theorem comp_zero_iff_forall_section_zero {X : Scheme.{u}} {M N P : X.Modules}
    (f : M ⟶ N) (g : N ⟶ P) :
    f ≫ g = 0 ↔ ∀ (U : X.Opens) (x : Γ(M, U)), g.app U (f.app U x) = 0 := by
  constructor
  · intro h U x
    have hx := congrArg (fun k ↦ k.app U x) h
    change g.app U (f.app U x) = 0 at hx
    exact hx
  · intro h
    apply Scheme.Modules.hom_ext _ _
    intro U
    ext x
    exact h U x

end AlgebraicGeometry.Scheme.Modules
