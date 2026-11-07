# Finite actual vertices of facets in the valuation quotient

This internal construction concerns supplied actual `ValuationBuildingData G`
over a nonarchimedean local field at every universe `u`. It uses the original
`B.ReducedBuilding`, its original rational-point action, its existing
`B.IsVertex` predicate and the existing combinatorial `buildingFacetClosure`.
The full apartment axioms and injectivity of the original apartment map remain
explicit hypotheses of the finite construction.

The definition `buildingFacetVertices Fc` consists precisely of the original
vertices in the closed facet. The definition `buildingFacetVertexFinset hD hinj Fc`
is a finite set with exactly the same membership. Each such set is nonempty.
In every original translated apartment presentation of `Fc`, this finset is
exactly the image of the entire affine-torsor vertex finset of the presenting
affine facet closure. Both the set and finset constructions respect the
original rational-point action.

Incidence implies vertex containment globally. The converse is proved for two
facets lying in one original translated apartment. Every lower facet of a
fixed upper facet lies in any original apartment containing that upper facet.
As a result, `finite_buildingFacets_below` proves that the set of all original
facets preceding any fixed facet is finite. It requires no global common
apartment theorem or supplied polysimplicial realization.

## Implemented argument

An original quotient vertex is represented by an original apartment vertex.
The latter has a singleton affine facet, so its image is a singleton building
facet. The facet partition under the apartment axioms identifies this singleton
with any chart facet through the same point. Chart injectivity then reflects
the singleton equality to the affine facet. Thus being an original building
vertex is preserved and reflected in every injective original chart.

The existing closed-facet image formula and this vertex equivalence identify
the entire vertex set in any facet presentation. The relative-root norm on the
original reduced translation space supplies a finite-dimensional real normed
space. These structures are installed only locally. The apartment is its
existing affine torsor, so `AffineTorsorFacetVertices` applies to the original
root system supplied by the full apartment axioms. Its finite nonempty set maps
to exactly the required quotient vertex set. Converting that finite set to a
finset proves the exact membership and chart formulas without choosing a new
carrier, action or vertex predicate.

The action formulas follow from the existing equivariance of closed facets
and the original `IsVertex.smul` in both group directions. Monotonicity follows
from monotonicity of closed facets. In a common chart, injective finite-set
mapping reflects containment, and the affine-torsor incidence theorem identifies
it with the original affine face relation. The existing quotient incidence
comparison converts this to the original `FacetPrecedes`.

To present a facet in a prescribed apartment containing it, choose one point
of the facet and lift it through that apartment chart. Uniqueness of the
containing facet identifies the whole facet with the chart facet at that lift.
This extends the incidence comparison from explicit presentations to any two
facets contained in a common original apartment.

Finally choose an original apartment containing the fixed upper facet. The
existing incidence theorem places every lower facet in that same apartment.
Its finite vertex set is a subset of the upper finite vertex set. Equality of
two such subsets gives incidence in both directions by the common-apartment
comparison, hence equality of the original facets by antisymmetry. The lower
interval therefore injects into the finite powerset of the upper vertex set.

## Provenance and scope

These are internal deductions from the existing quotient, facet partition,
closed-facet and incidence results, the relative-root translation norm, and the
finite actual affine-torsor vertex encoding. No new assertion from the
literature is introduced. Rank zero remains included, and no positive-root-rank
or nonempty-root-set premise is added.

The module does not assert that every subset of vertices is a face, that arbitrary
facets share an apartment, or that a simplex or product decomposition exists.
The apartment axioms, including AS5, and chart injectivity remain supplied.
It constructs neither general valuation data nor a polysimplicial realization
and does not prove any unconditional witness or the full statement
`RootValuationBuildingConstructionStatement`.
