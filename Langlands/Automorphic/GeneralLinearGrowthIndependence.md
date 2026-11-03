# Original general-linear growth spaces for arbitrary closed matrix embeddings

For an arbitrary number field `F`, a natural number `n`, and a matrix
representation `rho : GL_n -> GL_N` whose underlying scheme morphism is a
closed immersion, this module constructs comparisons with the original
`Langlands.Automorphic` matrix function spaces. The standard representation
of the actual general-linear group scheme is its identity morphism, hence
is itself a closed immersion.

The three complex linear equivalences
`polynomialGrowthGeneralLinearEquivOfClosedImmersion`,
`plotSmoothPolynomialGrowthGeneralLinearEquivOfClosedImmersion`, and
`finitePlotSmoothPolynomialGrowthGeneralLinearEquivOfClosedImmersion`
compose the published closed-embedding growth independence with the
published standard-representation comparisons. Their underlying ambient map
is exactly `continuousGeneralLinearEquiv`. The value formulas prove this
identity explicitly, and the action identities intertwine the original full
adelic right actions with the convention `R(g)f(x) = f(x*g)`, through
`GeneralLinearGroupPoints.adelicHomeomorph`.

The corresponding membership equivalences preserve and reflect the original
growth conditions. The polynomial growth predicate is quantified separately
on each fixed finite adelic slice: constants and exponent can depend on that
slice. The plot-smooth intersection also requires the existing infinite
coordinate-plot smoothness and finite-slice local constancy. The stronger
finite-plot-smooth intersection requires the existing common open finite
stabilizer. The two finite regularity conditions retain their distinct
quantifiers. The ambient-inclusion identity for polynomial growth and the
three value formulas retain the original continuous rational-function
realizations.

This is an internally derived consumer of
`GroupSchemeGrowthIndependence` and `GroupSchemeGrowth`. The implementation
first uses equality of the growth subrepresentations for `rho` and the
identity representation. For polynomial growth it composes the existing
identity change-of-representation linear equivalence with the original
standard comparison. For each smooth intersection it uses
`LinearEquiv.ofEq` for the corresponding submodule equality and then the
original standard comparison. The value formulas reduce these equality
casts to the original function, so the ambient action comparison gives the
three restricted action identities. No new external mathematical assertion
is used.

The construction retains arbitrary `F : Type u`, every `n` and `N`, including
zero, and the original topologies, matrix norms, quotient carriers and
actions. Its closed-immersion hypothesis is scheme-theoretic; injectivity
of a map on points does not replace it. It constructs no new embedding,
manifold, differential operators, uniform derivative-growth bound,
split-centre comparison, measure or integrability theorem. The comparison
does not discharge the remaining general-reductive reduction or
finite-volume obligations.
