# Proof of the binary affine-cover counterexample

`Langlands.Global.adelicAffineCoverCounterexample` proves exactly
`Langlands.Global.AdelicAffineCoverCounterexampleStatement` in arbitrary
common universe `u`.

Basic opens of the actual affine spectrum are affine. A prime ideal cannot
contain both t and 1-t, since their sum is one, so the binary opens cover the
scheme. The whole-space open of this affine scheme is also affine.

The actual open-subscheme lifting equivalence identifies a point image
with containment of its whole spectrum image in that open. Pullback of
D(1-t) by the actual affine-line point is the unit condition on 1 minus its
coordinate: evaluation commutes with subtraction and one, and an element
outside every maximal ideal is a unit. The published D(t) result supplies
the other half. The whole-space open contains every point image.

For number fields, a ring homomorphism sends a unit to a unit. The infinite
projection of the coordinate `(0,1)` is zero in the nontrivial actual infinite
adele ring, so the coordinate is not a unit. The ring of integers is not a
field; a nonzero maximal ideal supplies an actual finite place. The
complementary coordinate has zero image in that place's completed field,
so it is not a unit either. This argument retains every infinite factor.

For function fields, the actual chosen extension of the rational-function
place t=1 is distinct from the reference extension above t=0. Indeed,
restriction of their valuation subrings recovers the original subrings;
equality would give equality of the original places, contradicting
injectivity of `placeOfPoint` and `1 ≠ 0`. Evaluation of the actual
restricted product at the reference place sends the coordinate to zero.
Evaluation at the place above t=1 sends the complementary coordinate to
zero. Both completed fields are nontrivial, so neither coordinate is a
unit. The distinct-place and nonunit arguments work over arbitrary constant
fields with the original specified scalar tower. The actual `F`-relative
point uses the existing full-field diagonal, with finite constants as in
the target. No separability is used.

The coordinate equivalence and the generic unit-locus description now show
that each explicit point lies outside the binary point-image union.
Since the whole-space point-image union is every actual point, each
omitted point witnesses strict inclusion of the binary union in that
whole-space union. The final theorem combines the generic description and
both arithmetic results. No topological comparison is needed.

This is a derived concrete realization of Brian Conrad, *Weil and
Grothendieck approaches to adelic points* (December 31, 2011), printed p.9,
Example 4.1. The particular cover and coordinates are not specified in the
source. Registered source `conrad-2011-weil-grothendieck-adelic-points`,
SHA-256 `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
