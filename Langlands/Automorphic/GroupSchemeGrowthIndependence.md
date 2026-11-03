# Closed-embedding independence of actual adelic slice-growth spaces

For an affine group scheme over an arbitrary number field and two matrix
representations that are scheme-theoretic closed immersions,
`hasPolynomialGrowth_iff_of_closedImmersions` identifies the existing
slice-wise polynomial-growth predicates on
`GroupSchemeFunctions.ContinuousRationalFunctions`.
The proof applies the infinite adelic height comparison separately on
each fixed finite adelic slice. Each slice retains its own constants and
exponent; the result imposes no common bound across the finite slices.

`polynomialGrowthSubrepresentation_eq_of_closedImmersions` proves equality
inside the unchanged continuous rational-function representation.
`polynomialGrowthChangeRepresentation` gives the identity complex linear
equivalence of the existing growth subspaces. It commutes with their
original ambient inclusions and intertwines the full adelic actions
with formula `R(g)f(x)=f(x*g)`. The comparison changes neither the
rational invariance condition nor the topology on the ambient functions.

The existing intersections with plot smoothness and finite-slice local
constancy are equal for the two embeddings. The stronger intersections
using a common open finite stabilizer are equal as well, by rewriting
their growth factor. These remain distinct regularity conditions.

This is a derived consumer of
`RepresentationGrowthIndependence` and the existing actual slice-growth
construction. No additional external assertion is used. It does not
construct an embedding, identify differential operators, prove uniform
derivative growth or change the split-centre, measure or integrability
conditions. The existing standard-representation comparisons with the
original general-linear spaces continue to apply to these equal subspaces.
