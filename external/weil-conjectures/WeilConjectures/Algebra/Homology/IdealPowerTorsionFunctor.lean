/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Module.Torsion.PrimaryComponent

/-! # The ideal-power torsion functor

Source: Stacks Project, Tag 0BJA.
-/

@[expose] public section

universe u
open CategoryTheory

namespace ModuleCat

/-- The submodule of elements annihilated by some power of `J`, with maps obtained
by restricting the original linear maps. No object is selected from an existence theorem.
Source: Stacks Project, Tag 0BJA, the functor defining algebraic local cohomology.
(blueprint: def-sbc-ideal-power-torsion-functor). -/
def idealPowerTorsion {R : Type u} [CommRing R] (J : Ideal R) :
    ModuleCat.{u} R ⥤ ModuleCat.{u} R where
  obj M := ModuleCat.of R (Ideal.primaryComponent M J)
  map f := ModuleCat.ofHom (Ideal.primaryComponent.map J f.hom)
  map_id M := by
    ext x
    rfl
  map_comp f g := by
    ext x
    rfl

/-- Restriction to the ideal-power torsion submodules preserves addition of maps.
Source: Stacks Project, Tag 0BJA.
(blueprint: def-sbc-ideal-power-torsion-functor).
Proof: both sides send a torsion element x to f(x)+g(x), and subtype extensionality
identifies the resulting torsion elements. -/
instance idealPowerTorsion_additive {R : Type u} [CommRing R] (J : Ideal R) :
    (idealPowerTorsion J).Additive where
  map_add := by
    intro M N f g
    ext x
    rfl

end ModuleCat
