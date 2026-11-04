# A concrete failure of affine-open coverage on actual adelic points

`AdelicAffineCoverCounterexampleStatement` asks for a concrete realization of
Brian Conrad, *Weil and Grothendieck approaches to adelic points* (December 31,
2011), printed p.9, Example 4.1. Conrad states that an affine open cover need
not cover adelic points and that the union of its point images can depend on
the chosen affine cover. The particular affine-line cover and coordinates
below are derived constructions; the source does not specify them.

The generic component `AffineLineBinaryCoverDescriptionStatement` quantifies
over every commutative base ring `R`, including the zero ring. It asserts
that the actual basic opens D(t) and D(1-t) are affine and their supremum is
the whole actual affine line. The whole-space open is also affine, so it
gives a second affine cover. For every commutative `R`-algebra `S`, the union
of the two actual open-subscheme point images consists exactly of the points
whose coordinate or complementary coordinate is a unit. The image for the
whole-space cover is every actual point. These are statements about actual
relative scheme morphisms, using the published `affineLinePointEquiv`.

`NumberFieldAffineCoverCounterexampleStatement` retains the entire actual
full adele ring of every number field `K`, including all infinite factors.
It asserts that `numberFieldAffineCoverPoint K`, whose coordinate is
`(0,1)` in the infinite-times-finite decomposition, is outside the binary
point-image union, and that this union is strictly contained in the
whole-space point-image union.

`CurvePlaceAffineCoverCounterexampleStatement` retains every finite
constant field `k` and every function field `F` with the specified original
`k`-algebra, rational-function-field algebra and scalar tower. It assumes
no separability. The actual full restricted-product ring and original
`F`-diagonal action are used. The coordinate of
`curvePlaceAffineCoverPoint k F` is zero at the chosen actual place above
t=0 and one at every other actual place. The target asserts that this
explicit point is outside the binary union and that the binary union is
strictly contained in the whole-space union. Existence of a distinct
actual place, needed to show that the complementary coordinate is not a
unit, is a proof obligation rather than an assumed input.

The aggregate is the conjunction of these three proposition definitions.
It states a set-theoretic obstruction and does not assert a comparison of
topologies. Every quantified type lies in the arbitrary common universe
`u`. This unit states the assertions and does not supply their proof.

Registered source `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`,
printed p.9, Example 4.1.
