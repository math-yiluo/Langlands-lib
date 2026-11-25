/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace

/-!
# Morphisms of locally ringed spaces

A morphism of the underlying ringed spaces of two locally ringed spaces is a morphism of locally
ringed spaces if and only if all its stalk maps are local ring homomorphisms.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.LocallyRingedSpace

/-- **Morphisms of locally ringed spaces.** A morphism `(f, f^♯)` of the underlying ringed
spaces of two locally ringed spaces `X` and `Y` underlies a morphism of locally ringed spaces
`X ⟶ Y` (Mathlib's `AlgebraicGeometry.LocallyRingedSpace.Hom`) if and only if all stalk maps
`f^♯_x : 𝒪_{Y, f x} → 𝒪_{X, x}` are local ring homomorphisms.

(blueprint: `def-weil-locally-ringed-space-morphism`) -/
theorem exists_toHom_eq_iff {X Y : LocallyRingedSpace.{u}}
    (f : X.toPresheafedSpace.Hom Y.toPresheafedSpace) :
    (∃ g : X ⟶ Y, g.toHom = f) ↔ ∀ x, IsLocalHom (f.stalkMap x).hom :=
  ⟨by rintro ⟨g, rfl⟩; exact g.prop, fun h ↦ ⟨⟨f, h⟩, rfl⟩⟩

end AlgebraicGeometry.LocallyRingedSpace
