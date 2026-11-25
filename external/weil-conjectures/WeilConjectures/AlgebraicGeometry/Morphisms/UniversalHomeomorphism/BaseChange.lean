/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism

/-!
# Base change of universal homeomorphisms

Any base change of a universal homeomorphism of schemes, i.e. the parallel side of an
arbitrary pullback square, is again a universal homeomorphism. This is the stability of the
class `AlgebraicGeometry.IsUniversalHomeomorphism` under base change, stated for a pullback
square rather than for the chosen pullback.

## Main statements

- `AlgebraicGeometry.IsUniversalHomeomorphism.of_isPullback`: base changes of universal
  homeomorphisms are universal homeomorphisms.
-/

@[expose] public section

universe u

open CategoryTheory Limits MorphismProperty

namespace AlgebraicGeometry.IsUniversalHomeomorphism

/-- **Base change of universal homeomorphisms**: in a pullback square
```
  Y' ──f'──→ Y
  │          │
  g'         g
  ↓          ↓
  X ───f───→ S
```
if `g` is a universal homeomorphism, then so is its base change `g'`. -/
theorem of_isPullback {X Y Y' S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {f' : Y' ⟶ Y}
    {g' : Y' ⟶ X} (sq : IsPullback f' g' g f) [IsUniversalHomeomorphism g] :
    IsUniversalHomeomorphism g' :=
  MorphismProperty.of_isPullback (P := @IsUniversalHomeomorphism) sq inferInstance

end AlgebraicGeometry.IsUniversalHomeomorphism
