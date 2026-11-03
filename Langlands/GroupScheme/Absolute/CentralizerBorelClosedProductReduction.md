# The centralizer Borel theorem from closed products and quotient properness

Internal assembly by Worker 1438. Worker 1479 supplied the actual-intersection
geometry and the restriction argument applying dynamic connectedness inside
the Borel. The included unchanged homogeneous closed-immersion helper credits
Worker 716 for the adapted generic-flatness covering argument.

This module specializes the actual quotient and closed-product machinery to
the unchanged scope of `CentralizerBorelIntersectionStatement`. The base field
and universe are arbitrary unless algebraic closedness is explicitly imposed.
The cocharacter may be trivial or noninjective, and the closed centralizer
representative is the supplied map `j`.

`IsBorelSubgroup.centralizerIntersectionQuotient` chooses an actual homogeneous
quotient of the actual pullback intersection. Its smoothness comes from
`centralizer_intersection_properties`; affineness of the centralizer follows
from the given closed inclusion into the affine ambient group. The chosen
quotient retains every field of the published `HomogeneousQuotient`
structure, including exact coset fibers on every relative test scheme.

Over an algebraically closed field, with the ambient and centralizer
smoothness and connectedness required by the original target, the
`centralizer_intersection_isBorel_of_closed_product` theorem proves Borel
maximality of the actual first projection under three explicit inputs:

- `ParabolicSubgroupQuotientProperStatement`;
- `ProperSolvableQuotientBorelStatement`;
- closedness of the actual multiplication image of the centralizer and the
  prescribed Borel in the ambient group.

The geometry module supplies closedness, smoothness and solvability of the
intersection. To prove its connectedness, the cocharacter is restricted to the
given Borel. The actual second projection represents its internal centralizer,
so the published `dynamicConnected` theorem applies to that smooth affine
connected Borel. Thus no additional intersection-connectedness hypothesis is
assumed.

The prescribed Borel has a chosen actual homogeneous quotient. The proved
algebraically closed Borel-to-parabolic bridge and the first explicit input
make this quotient proper. The actual comparison from the chosen
intersection quotient is a closed immersion by the closed-product properness
construction, making that quotient proper as well. The second explicit input
then proves that the actual first projection is Borel.

`exists_centralizer_borel_of_closed_product` uses that actual intersection as
the desired Borel and the pullback range identity for its prescribed
containment on every test scheme. Finally,
`centralizerBorelIntersection_of_closed_products` quantifies this construction
over precisely the original target's hypotheses and returns the published
`CentralizerBorelIntersectionStatement`, conditionally on the two named
proper-quotient statements and closedness for all these actual products.

These three inputs are not proved here. In particular, this internal reduction
is not an unconditional proof of the host target. No reductivity, maximal
torus, characteristic, splitting or injectivity condition is added to its
scope, and no published statement or imported pair is changed.
