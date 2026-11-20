# Hausdorffness and rational-point injectivity from separatedness

`SeparatedAnalytificationProperties p` asserts that the underlying space of the
analytic target is Hausdorff and that `rationalPoint p P₀` is injective for every
finite polynomial presentation of the base field. The theorem
`IsAnalytification.separatedAnalytificationProperties` proves both conclusions
for an analytification of a separated algebraic space over a complete,
nontrivially normed ultrametric field.

For the closedness argument, let `f : A →ₐ[K] C` and `g : B →ₐ[K] C` induce a
surjection `A ⊗[K] B →ₐ[K] C`. The theorem
`isClosedMap_pair_baseMap_of_surjective` proves that the joint point map from the
affine analytification of `C` to the ordinary product of the affine
analytifications of `A` and `B` is closed. A tensor expression for a coordinate
generator of `C` gives a continuous upper bound on its seminorm in terms of
the two projected points. For a pure tensor this bound is the product of the
two seminorm evaluations. For a sum the bounds add by the seminorm triangle
inequality.

Take a point in the closure of the image of a closed source set. A common
radius strictly above all the finitely many bounds at this point gives an open
neighborhood where the bounds stay below that radius. All source points
mapping into the neighborhood lie in the corresponding bounded chart.
Intersecting the chart with the closed source set gives a compact set whose
image in the Hausdorff product is closed. The closure point therefore belongs
to this compact image.

The theorem `isCompact_preimage_pair_baseMap_of_surjective` uses the same
continuous bounds on a compact subset of the product. Each bound has a finite
upper bound there. A single radius then contains its entire inverse image.
This inverse image is closed by continuity and Hausdorffness of the product,
so it is compact as a closed subset of that chart.

For Hausdorffness, each pair of affine étale charts admits a pullback with
coordinate algebra a quotient of the tensor product. The analytification
pullback and ordinary point lifting identify the range of the joint map with
the equality relation on the two chart spaces. The closed map result makes
this relation closed. Étale openness and joint surjectivity then give
Hausdorffness by `IsAnalytification.t2Space_iff_affineEtaleChartRelationsClosed`.

For injectivity, `rationalPoint_injective_of_pointLifting` applies to the same
ordinary point lifting theorem. This compares two base-field points with equal
analytic image through their algebraic and analytic pullbacks.

This is an internal consequence of the Library's finite-presentation affine
charts, seminorm evaluations, separated affine pullbacks, and point lifting.
