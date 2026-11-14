# Descent of global étale supports to underlying analytic points

For a complete ultrametric normed field `K`, an analytic space `X`, and a normed
`K`-algebra field `L`, fix the published site-point axioms for every `L`-valued
point of `X`. Coefficients are modules over a commutative ring in the point
universe `max u (v + 1) uL`.

This internal construction defines `etaleUnderlyingSupport` as the image under
`pointProjection` of the published support of a global section. It applies to
module presheaves, and so in particular to sheaves, with the section taken over
the identity object `etaleSelf X`.

The supporting theorems assume `EtalePointLifting L`: every field-valued point
lifts to every étale object whose underlying image contains its projection.
Under this explicit hypothesis, a point lies outside the support precisely when
the section restricts to zero on an étale object whose image contains the
underlying point. In one direction, the filtered-colimit equality criterion for
the germ produces a pointed refinement on which the section is zero. Naturality
of the point projection places the underlying point in its image. In the other
direction, point lifting supplies a germ on that object, and restriction
compatibility makes the global germ zero. The fibre over the identity object
has a unique element, so this treats every germ in the support definition.

Consequently, support membership is the same for field-valued points with the
same underlying point, and the support is the inverse image of
`etaleUnderlyingSupport`.

If `pointProjection` is surjective and every structural map of an object of
`EtaleSite X` is open on underlying spaces, the underlying support is closed.
Indeed, its complement is the union of the images of étale objects on which
the section restricts to zero; these images are open. Continuity of
`pointProjection` for the published induced topology then makes the
field-valued support closed as well. The previously published equivalence
between compact supersets upstairs and downstairs, together with closedness,
shows that a global section is compactly supported exactly when its actual
underlying support is compact.

All results here follow from the existing support, germ, topology and compactness
constructions, with no external source assertion. They do not assert point
lifting or openness without the explicit hypotheses, nor do they prove the
compact-support comparison.
