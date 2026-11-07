# Universal open neighborhoods from a finite map with AF source

Author: Worker 133.

This internal construction proves the point-containment part of the
finite-surjective AF descent shrinking argument. It works over an arbitrary
scheme base, with a finite represented transformation from an actual scheme
to any presheaf. Surjectivity and target representability are unnecessary
for these particular conclusions.

## Represented tests and finite point sets

In namespace
`Langlands.AlgebraicGeometry.AlgebraicSpace.FiniteAffineUniversalNeighborhoods`,
`sourceOverTest hπ a` is the actual scheme representing the inverse image
of a scheme test under a finite map `π`. `sourceProjection` and
`testProjection` are actual morphisms over the original base. The first
uses fullness of the relative scheme Yoneda functor.
`sourceOverTest_square` proves the cartesian square in presheaves, and
`testProjection_isFinite` applies the existing represented finiteness
predicate to this square.

For a test `Spec K` with `K : Type u` a field,
`finite_sourceProjection_range` proves that the range of the projection
into the original source scheme is finite. The proof uses that `Spec K`
has finitely many underlying points and that a finite scheme morphism has
finite preimages of finite sets, and then takes the image of that finite
set under the source projection. No algebraic-closure assumption on `K`
or closed-point restriction on the source is used.

## Universal target opens

`mem_universalImage_of_range_subset` takes any actual represented pullback
of a test and an actual source open immersion `j`. If the entire point
range of its source projection lies in `j`, then the test's section lies
in the universal image of the range of `j`.

The implemented proof first factors the source projection through the
open immersion using the point-range criterion. Thus the range of its
Yoneda transformation is contained in the range of `j`. The pullback
square identifies this range with the inverse image of the test chart's
range. The adjunction between inverse image and `universalImage` gives
the desired containment, evaluated at the identity test section. This
argument includes arbitrary further base changes through the definition
of universal image.

`affineOpenTest` and `affineOpenInclusion` equip an actual affine open in
the source scheme with its original base map and its inclusion.
`universalAffineOpen π V` is the largest target subfunctor whose inverse
image lies in that affine source open. It is a representable open
subfunctor when `π` is finite, by the published
`OpenSubfunctorDescent.universalImage_open_of_finite`.

`exists_universalAffineOpen_of_field_test` assumes the existing AF
property of the actual source scheme. For every actual field-valued
scheme test of the target, it produces an affine source open whose
universal target open contains that test's section. The proof applies AF
to the finite source-projection range established above and then uses the
universal-image membership lemma.

All results are internal consequences of the named Library constructions
and Mathlib's scheme finiteness results. This module does not make the
inverse image of a target open affine. A later quasi-compact shrinking
only makes it quasi-affine, so an independently proved quasi-affine-source
AF descent theorem remains necessary for the intended route. No final
scheme representation or full AF-descent theorem is supplied here.
