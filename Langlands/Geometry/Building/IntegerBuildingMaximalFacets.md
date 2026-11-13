# Maximal facets in prescribed subsets of the integer-valued building

For supplied `IntegerValuationBuildingData v G` over an arbitrary field,
every full facet in any specified subset of full facets has a maximal
extension within that subset. Incidence is exactly the original
`FacetPrecedes` relation. The statement is universe polymorphic and imposes
no characteristic restriction, local-field assumption or additional
apartment axiom.

The Prop-valued `IntegerBuildingMaximalFacetsStatement` quantifies over the
field, integer-valued valuation, affine group scheme, supplied building
data `B`, a set `s : Set B.BuildingFacet`, and `F ∈ s`. It asserts existence
of `C ∈ s` with `B.FacetPrecedes F C`, such that every `E ∈ s` satisfying
`B.FacetPrecedes C E` equals `C`. `integerBuildingMaximalFacets` proves this
exact statement. The data already supply connected reductivity, a maximal
split torus and the compatible actual KP apartment; their existence is
not asserted here.

The proof constructs a natural count on the original reduced quotient and
then its full facets. This is the number of actual affine roots vanishing
at a point in apartment coordinates. It counts affine functionals, not
codimension. The finite derivative-root set follows directly from the
finite set of actual relative roots of the supplied maximal split torus:
every actual affine root has the derivative `rootForm B.i α` for such a
relative root `α`. Finiteness uses the published
`IsSplitTorus.finite_relativeRoots`, with local finite type supplied by
smoothness of the connected reductive group.

`pointVanishingRootCount` uses `Quotient.lift` on the original quotient of
`G(k) × B.Apartment`. For two related pairs, the original quotient relation
supplies a normalizer element carrying the first apartment point to the
second. The existing actual normalizer root-preservation theorem and
`AffineRootSystem.vanishingRootCount_apply` show that their counts agree.
Thus every translated apartment computes the same quotient count, without
any choice of a new point space or equivalence relation.

The quotient count is constant on full facets because apartment root counts
are constant on sign facets. `facetVanishingRootCount` chooses a point of a
nonempty full facet; constancy proves that every point and every translated
apartment presentation computes its value. For distinct incident full
facets, their common-chart affine facets must be distinct, since equal
coordinate facets have equal images. The strict affine face inequality
from `AffineFacetRootCount` therefore gives a strict decrease of the count
in the upward direction.

Finally, minimize this natural count over all members of `s` incident above
`F`. That collection contains `F` by reflexivity. If the minimizing `C` had
a distinct incident upper facet `E` in `s`, incidence transitivity would put
`E` above `F` as well, and strict count decrease would contradict
minimality. This proves maximality inside the whole subset `s`.

This is an internal deduction. Its actual inputs are the original
integer-valued quotient and facet definitions, actual normalizer root
preservation from `IntegerBuildingFacetPartition`, the order and
transitivity from `IntegerBuildingFacetOrder`, the affine count lemmas in
`AffineFacetRootCount`, and relative-root finiteness. No new external
source theorem is asserted.

The chosen subset need not contain every upstairs facet. In particular,
maximality in that subset does not claim that the resulting facet is an
ordinary upstairs chamber. This module constructs no descended model,
residue-parabolic correspondence or torus lift and does not prove the
prescribed-point split-torus theorem.
