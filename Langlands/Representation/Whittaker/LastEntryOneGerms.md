# Root coefficients and coordinate germs

Author: Worker 186.

These are internal adapters for the last-entry-one proof.
This module uses the published JPS function spaces and the independently
published kernel, center-span and upper-support proofs. It does not prove the
function-space decomposition.

`operatorSpan_finite_of_surjective` transfers finite-dimensional operator
span through a surjective intertwiner. Postcomposition with the intertwiner
maps the original finite operator span into a space of linear maps. On the
image representation, precomposition with that surjection is injective and
maps its operator span into the former finite-dimensional image.

`rootCoefficientToSpace` corestricts the actual root coefficient map to its
invariant image. Composing with the published canonical germ projection gives
`rootGermMap`, a surjective intertwiner. Its kernel is precisely uniform
near-zero vanishing in the selected coordinate. Restricting its intertwining
identity to a coordinate embedding gives `rootGermMap_coordinate`.

`jacquetToRootGerm` is conditional on uniform coordinate vanishing for every
vector killed by the actual Jacquet projection. It factors the actual
coefficient-to-germ map through that projection. These are derived algebraic
adapters for the quotient comparison in JPS (1979), Proposition (2.2), printed
pp.181–183, registered source `jps-1979-gl3-i`. No supplied kernel condition is
claimed as a proved Whittaker vanishing theorem.

`rootLift_coordinateEmbedding` computes a single-coordinate cumulative-product
lift by checking its consecutive quotients and final entry. The resulting
matrix is identified with the actual two-block scalar `(b,1)` in
`torus_rootLift_coordinateEmbedding`. The comparison uses the standard block
index equivalence and the published formula for an embedded block scalar.
`jacquetToRootGerm_mk` records the representative law of the conditional
factorization; its surjectivity follows from the original coefficient-to-germ
surjection.

`operatorSpan_finite_comp` restricts a representation along a monoid homomorphism
by inclusion of its operator span. `coordinateJacquetRepresentation` is the
actual unnormalized product-Levi Jacquet action restricted to the scalar tuple
`(b,1)`. Its representative formula is definitional. The conditional
`coordinateJacquetToRootGerm` is a surjective intertwiner, using the preceding
matrix comparison. `rootCoefficientSpace_finiteCoordinateOperatorSpan`
therefore transfers the finite span of **all** actual block-scalar operators to
the coordinate-germ action. Both the Jacquet-kernel vanishing and all-block
finite-span assertions remain explicit premises in this adapter; no scalar
central-character substitute is used.

`rootCoefficient_kernel` applies the independently published
`Whittaker.coordinateJacquetKernelStatement` theorem to discharge the kernel
premise above for the actual Whittaker data.
It specializes the full-diagonal conclusion to the cumulative-product lift
and uses `rootHom_rootLift` to identify its selected adjacent ratio with
the selected coordinate. The positive threshold is unchanged and remains
uniform in every other root coordinate.

`rootCoefficientSpace_finiteOperatorSpans` combines this
converter with the published `Parabolic.jacquetCenterSpan` theorem.
It applies the latter to the actual two-block Jacquet quotient in each
coordinate, restricts the all-block scalar action to `(b,1)`, and descends
the finite span through the surjective intertwiner. Thus finite operator spans
are proved from the original admissibility, finite generation and Whittaker
data. Smoothness needed for kernel vanishing follows from admissibility; no
hypothesis on the central character is added.

`rootCoefficientSpace_isSmoothSpace` and
`rootCoefficientSpace_isLocallyConstantSpace` put the already proved
smoothness and pointwise local constancy into the two distinct published
JPS predicates. `rootCoefficientSpace_hasCoordinateUpperSupport_of_statement`
converts the raw upper-support adapter into the JPS coordinatewise predicate.
It uses the same positive bound for every coordinate of a fixed function,
and that bound is uniform over all coordinate tuples.

`rootCoefficientSpace_hasCoordinateUpperSupport` discharges that support
premise using the independently published theorem
`Whittaker.smoothSimpleRootSupport`. Thus this upper-support conclusion is
unconditional for the stated smooth Whittaker data. Its topology is the supplied
`T`, so it applies in particular with the canonical topological data of the
parent target. Neither the kernel theorem nor the center-span theorem is an
additional premise in these final Whittaker specializations.
