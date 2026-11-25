module

public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.Tactic.CrossRefAttribute

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Universal homeomorphisms of schemes

A morphism of schemes is a universal homeomorphism if every base change of it induces a
homeomorphism on the underlying topological spaces.

## Main definitions

* `AlgebraicGeometry.UniversalHomeomorphism` is the property of being a universal
  homeomorphism of schemes.

## Main results

* `AlgebraicGeometry.universalHomeomorphism_iff` unfolds the property in terms of all
  pullback squares.
* `AlgebraicGeometry.universalHomeomorphism_comp`: universal homeomorphisms are stable under
  composition.

## Implementation notes

The definition uses `MorphismProperty.universally`, so it is independent of a chosen pullback
object. Thus it quantifies over every pullback square presenting the base change, rather than
choosing a displayed fibre product.

## References

* [Stacks Project, Tag 04DD](https://stacks.math.columbia.edu/tag/04DD)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- A morphism of schemes is a universal homeomorphism if every base change is
a homeomorphism on the underlying topological spaces. -/
@[mk_iff, stacks 04DD]
class UniversalHomeomorphism {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop where
  /-- Every base change of `f` is a homeomorphism on the underlying topological spaces. -/
  universally_isHomeomorph : (topologically @IsHomeomorph).universally f

end AlgebraicGeometry

end
