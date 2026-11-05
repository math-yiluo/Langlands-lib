# Divided powers recovered from polynomial point actions

This internal extension supplies explicit inverse-Vandermonde coefficient
weights. For distinct field elements, those weights recover every vector
coefficient of a bounded-degree polynomial from its sampled values. Over an
infinite field, a vector subspace containing every value therefore contains
every coefficient. The proof multiplies the sampled-value matrix by the
inverse Vandermonde matrix, then uses closure of the subspace under linear
combinations.

The concrete families `upperMatrix` and `lowerMatrix` sum the rank-one raising
and lowering divided powers with the appropriate powers of the parameter.
`invariantOfPolynomialStable` constructs a divided-power invariant subspace
from stability under every matrix in these polynomial families. Coefficient
reconstruction handles the degrees at most the weight; the higher divided
powers are zero.

Finally `PolynomialRootRealization` records actual elements of a represented
monoid whose operators are these two polynomial families at a Steinberg
weight. The module proves irreducibility of any supplied representation with
such a realization, using the explicit rank-one divided-power simplicity
calculation. This is ordinary representation irreducibility under all monoid
elements, the notion used for the rational-point representation in the
big-cell target.

The module does not assert that such a realization exists for a group scheme,
prove group laws for the two polynomial matrix families, or identify any
induced covariant coordinate space. It assumes no irreducibility theorem.
Its provenance is internal finite-dimensional linear algebra and the explicit
rank-one operator formulas; higher-rank highest-weight theory remains open.
