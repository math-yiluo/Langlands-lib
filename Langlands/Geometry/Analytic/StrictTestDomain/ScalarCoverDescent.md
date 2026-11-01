# Scalar descent for fixed families of actual rational quotients

This is an internal interface and formal transport construction. It defines
`CompatibleScalarSections`, `ScalarCoverSeparated`, `ScalarCoverDescent` and
`UniversalScalarCoverDescent` for an arbitrary indexed family of actual
`RationalData` over a presented strict affinoid algebra. Compatibility uses the
actual `interLeft` and `interRight` restrictions for every ordered pair.
Descent means unique scalar lifting along the actual base maps. Universal
descent quantifies over every bounded map to a presented strict affinoid base.
The index universe is independent of the field universe.

No definition asserts that any particular family has descent or separation.
Neither finiteness nor a covering hypothesis is built into these predicates;
the empty-family descent assertion consequently entails that the base has one
element. Zero and nonreduced bases and empty rational loci are permitted.

The formal compatibility and refinement arguments adapt Worker 146's
unreviewed `WholeSpectrumRefinementAdapter`, shared revision 4. Worker 572 adds
the named predicates, arbitrary-index base-change compatibility, and the
actual bounded maps between inverse-image quotients. Both workers are
coauthors. The mathematical provenance is internal: these are consequences
of the published rational representation and bounded extension theorems,
rather than translations of a separately claimed literature theorem.

`compatible_sections_apply` constructs a map from the actual intersection
quotient to any common presented target over the base. Uniqueness of maps out
of each rational quotient identifies its composites with the given maps, so
intersection compatibility implies equality in that target.
`CompatibleScalarSections.comparison` transports compatibility by the
published intersection comparison and its two restriction squares.
`ScalarCoverDescent.separated` applies uniqueness to the family of images of
one base element.

`ScalarCoverDescent.of_refinement` restricts the original sections to the
refining family, checks compatibility using the common-target argument and
glues them using the explicit descent premise. It then uses the explicit
separation premise on the pullback refinement over each original quotient to
verify the original lift equations. Uniqueness follows from uniqueness on the
refinement. In particular, this result supplies no unproved analytic
refinement-descent theorem.

`RationalData.pullbackTriangleMap` constructs the bounded map of inverse-image
quotients in a commuting triangle of presented bases using
`RationalData.extension`. Its base-map and comparison squares follow from the
two proved extension squares. `pullbackSwapMap` applies the same construction
to exchange the bases of two rational quotients. Applying it to a scalar lift
equation gives `pullback_base_images_eq`, an equality on the exchanged actual
pullback. No substitute quotient carrier or assumed comparison is used.

The scope is scalar transport at the existing unit radii over complete
ultrametric normed fields. This module proves no standard-cover descent,
higher Cech exactness, admissibility, finite-module descent or arbitrary-radius
assertion.
