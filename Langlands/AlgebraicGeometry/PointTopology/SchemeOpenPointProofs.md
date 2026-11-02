# Open-chart and functoriality proof on actual scheme points

This unit proves the complete target
`Langlands.AlgebraicGeometry.PointTopology.SchemeOpenPointProperties`
through `schemeOpenPointProperties_proof`. It uses the actual `RingPoint`
carrier, actual open subschemes and the explicit `schemePointTopology`
constructed from all affine charts. The hypotheses are precisely those of the
target: local commutative `S`, continuous multiplication and `IsOpenUnits S`,
with `Algebra R S` and a topology only on `S`. The schemes are arbitrary, and
no finite-type or separation assumption is introduced.

## Implemented local and functoriality argument

`relativeOpenLift` factors an actual relative scheme morphism through an open
subscheme when its entire image lies there. It is Mathlib's open-immersion
lift, with the base equation proved explicitly; `relativeOpenLift_fac` proves
its composition with the open inclusion equals the original morphism.

`continuous_affineToSchemePointMap` considers a map from an affine source
scheme to any target scheme. At an actual point, choose an affine target chart
containing the image of the closed point of `Spec S`. Choose an affine open
neighborhood of the source closed-point image inside the inverse image of
that target chart. The relative open lift gives an actual map between these
affine schemes, continuous on their evaluation-topologized point spaces.
The target chart map is continuous by definition of the final topology.
Their composite agrees exactly with the original point map after restriction
to the source affine neighborhood. The source neighborhood point inclusion is
an open embedding by `AffineOpenEmbeddingProofs`, and the local-ring
containment criterion lifts the original point into it. Continuity at that
lifted point therefore proves continuity at the original point.

`schemePointContinuity_proof` now handles arbitrary sources: the inverse
image of an open subset in the final target topology is open in every affine
source chart by the affine-source result. The defining open-set criterion for
`schemePointTopology` proves that inverse image open globally. Actual
postcomposition and its associativity are used in every map comparison.

## Implemented arbitrary-open embedding argument

`isOpenMap_schemeOpenPointMap` proves that an actual open-subscheme inclusion
is open for the final topologies. Test the image of an open set in each
ambient affine chart. A point in this inverse image has its closed-point
image inside the given open subscheme. In the ambient chart choose an affine
neighborhood lying in that open subscheme. Its actual point inclusion into
the chart is an open embedding by the affine-open result. Its actual map to
the given open subscheme is continuous by the affine-source result above.
The open image of the inverse image of the original open set therefore gives
an open neighborhood contained in the chart-tested image. Localness lifts
the original point to this neighborhood; monomorphism injectivity and exact
postcomposition identities identify its value in the open subscheme with
the given point. This proves openness in every affine chart, hence openness
in the final ambient topology.

`schemeOpenPoint_proof` combines this open-map result, the functoriality
result and actual open-immersion point injectivity into an open embedding.
`schemeOpenPointProperties_proof` combines it with the general affine-open
result and functoriality to prove exactly the grouped target. The proof uses
no assumed chart-compatibility field, alternate point carrier or unspecified
topology. Uniqueness, fiber products, closed immersions and the nonaffine
separation/local-compactness conclusions are outside this target.

The target is published in `SchemeOpenPointStatements`. This proof and
`AffineOpenEmbeddingProofs` are submitted together as a focused proof unit;
the helper pair is required alongside this entry pair. The source motivating
the target is Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), Proposition 3.1 and proof, printed page 4. The registered
source is `conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The derived relative scope is inherited from the published target.
