/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality
import WeilConjectures.AlgebraicGeometry.Exceptional.ExceptionalBaseChangeAffineLocality
import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.SmoothBaseChange

/-! The upstream sync moved the smooth base-change theorem and added quasi-separatedness.
This module keeps the earlier statement under a new name for Sheaf users. -/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X Y : Scheme.{u}}
  [HasInvertibleExponent Λ X]
  (f : X ⟶ Y) [HasCompactification f] (d : ℕ) [SmoothOfRelativeDimension d f]

include d in
/-- Blueprint `proposition-exceptional-inverse-image-smooth-morphism--6` without the
quasi-separatedness of the base: the canonical morphism `Lg'^* Rf^! ⟶ Rf'^! Lg^*` is an isomorphism
for `f` smooth of relative dimension `d` and quasi-compact `f'` (the statement of
`isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension` before the sync).
(blueprint: proposition-exceptional-inverse-image-smooth-morphism--6) -/
theorem isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension_general
    {X' Y' : Scheme.{u}} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : IsPullback g' f' f g)
    [HasCompactification f'] [QuasiCompact f'] :
    IsIso (rightDerivedUpperShriekBaseChangeMap Λ sq) := by
  apply isIso_rightDerivedUpperShriekBaseChangeMap_of_affine_open Λ sq
  intro U V j _ _ a p sqU _ V' U' b p' c sq' _ _
  have : SmoothOfRelativeDimension d p :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := d)).of_isPullback sqU
      inferInstance
  have : HasInvertibleExponent Λ V := HasInvertibleExponent.of_hom a
  exact isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension Λ p d sq'

end AlgebraicGeometry.Etale
