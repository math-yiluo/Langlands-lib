# Covering and nerve for the star neighborhoods

This is an internal reduction of the published
[`DistinguishedCoveringStatement`](DrinfeldCoveringStatement.lean). It proves
the covering, computes the nerve on the building, and shows how to assemble
the exact target from two additional analytic inputs. The proof does not
identify the norm model with a realization of a simplicial complex.

## Building-side bound

`NormClass.nerveRadius ϖ N = log (gapConst ϖ N) = log q / N`, where
`q = ‖ϖ‖⁻¹`, is the strict additive upper bound used in the nerve argument.
It is positive for a uniformizer `ϖ` and `N > 0`. If `ε` is below this bound
and `x ∈ vertexNbhd e ε`, choose `y ∈ vertexStar e` with
`distRatio x y < exp ε`. The distance bound of
[`DrinfeldNearestVertex.lean`](DrinfeldNearestVertex.lean) gives
`distRatio y e ≤ q / gapConst ϖ N` in dimension `N`. The multiplicative
triangle inequality and `exp ε < gapConst ϖ N` give `distRatio x e < q`.

Thus if the neighborhoods of a nonempty finite set of vertices meet,
all those vertices are strictly within multiplicative distance `q` of one
point. `isFacet_of_distRatio_lt` identifies the set as a facet. Conversely,
[`DrinfeldFacetBarycenter.lean`](DrinfeldFacetBarycenter.lean) puts the
barycenter of a suitable chain representing a facet in every one of its
vertex stars. For `ε > 0` those stars are contained in their neighborhoods,
so the neighborhoods intersect.

## Pullback to Drinfeld's upper half space

`iUnion_facetDomain_singleton` proves the covering for every `ε > 0`, with
no analytic premise: the reduction of a point has a nearest vertex, and
therefore belongs to that vertex's neighborhood. This puts the original
point in the singleton facet domain, by the definition as a preimage.

`distinguishedCovering_of_surjective_of_distinguished` takes the exact
propositions `ReductionSurjectiveStatement` and `FacetDomainDistinguishedStatement`
as hypotheses. Surjectivity transfers the building-side nonemptiness
equivalence to the preimage. The compact analytic difference witnesses come
from the second hypothesis. The proof uses `min εd (nerveRadius ϖ N)` as
the common positive bound, where `εd` comes from the second hypothesis
and `N = dim_F F^{d+1}`. The two hypotheses are not discharged here; the
module proves neither surjectivity nor the analytic distinction of the domains.
