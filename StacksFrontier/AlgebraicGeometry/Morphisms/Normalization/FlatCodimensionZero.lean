module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.Tactic.CrossRefAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.SchemeProperty.UniversallyInjective

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Codimension-zero points and local finiteness along a flat morphism of finite type

The normalization of a scheme is defined only under the hypothesis that every quasi-compact
open has finitely many irreducible components, and the functoriality of the normalization
requires in addition that generic points of irreducible components be carried to generic
points of irreducible components. Both conditions ascend along a flat morphism locally of
finite type. For algebraic spaces these are the two conclusions of Tag 0GMD, whose first
condition is the one of Tag 0BB1 and whose second is Tag 0GMC; the statements proved here
are the representable cases of all three, in which — as Tag 0BB1 itself records — the
condition of Tag 0BB1 reads literally "every quasi-compact open has finitely many
irreducible components", and a point has codimension `0` exactly when it is the generic
point of an irreducible component.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.mem_genericPoints_of_flat`: a flat morphism of schemes carries generic
  points of irreducible components to generic points of irreducible components. This is the
  representable case of Tag 0GMC, and the second conclusion of Tag 0GMD in the representable
  case.
* `AlgebraicGeometry.finite_irreducibleComponents_of_flat_locallyOfFiniteType`: if every
  quasi-compact open of the target of a flat morphism locally of finite type has finitely
  many irreducible components, then so does every quasi-compact open of the source. This is
  the first conclusion of Tag 0GMD in the representable case.

## Implementation notes

Irreducible components of a scheme correspond to its generic points, so both statements are
proved by counting and transporting generic points. A flat morphism is generalizing, and a
generalizing map between sober spaces carries generic points to generic points; this gives
the second statement outright and is the first step of the first one. For the first
statement, over a generic point of the target the generic points of the source lying above
it are the generic points of the scheme-theoretic fibre, and the fibre of a morphism
locally of finite type over a field is a Noetherian scheme and so has finitely many of
them. This bounds the generic points of an affine piece of the source by a sigma type over
the generic points of the target, and a quasi-compact open is covered by finitely many such
pieces.

The hypothesis and conclusion of the first statement quantify over quasi-compact opens
rather than assuming the schemes themselves quasi-compact. That is what makes the statement
local, and what lets it be applied to the affine pieces of the covering during its own
proof.

## References

* [Stacks Project, Tag 0GMD](https://stacks.math.columbia.edu/tag/0GMD)
* [Stacks Project, Tag 0GMC](https://stacks.math.columbia.edu/tag/0GMC)
* [Stacks Project, Tag 0BB1](https://stacks.math.columbia.edu/tag/0BB1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0GMC, representable case.** A flat morphism of schemes carries a
generic point of an irreducible component of its source to a generic point of an irreducible
component of its target. Equivalently, it carries codimension-zero points to
codimension-zero points, which is the second conclusion of Tag 0GMD. -/
@[stacks 0GMC "representable case"]
public theorem mem_genericPoints_of_flat {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    {x : X} (hx : x ∈ genericPoints X) : f x ∈ genericPoints Y :=
  genericPoints_map_of_generalizingMap f (Flat.generalizingMap f) hx

end AlgebraicGeometry

end
