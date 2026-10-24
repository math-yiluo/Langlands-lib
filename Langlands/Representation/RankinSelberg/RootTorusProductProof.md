# Proof of the uniform finite-family product reduction

`Langlands.RankinSelberg.rootTorusProduct` proves
`RootTorusProductStatement F T n` with its full field universe, supplied
topological data, and every natural number `n`.

For the fixed input sets `X` and `Y`, the finite family in the statement is
already explicitly defined. Applying `rootCoordinateFiniteFunction` to each
pair of members proves its continuity and finite-dimensional translation
span. This step precedes the choice of any test data.

Given the two families of root tests, the row test and `k`, the proof applies
`rootSchwartzAssembly` independently to each pair of indices and chooses
the resulting Schwartz functions. The root-coordinate theorem rewrites the
adjacent diagonal ratios as root coordinates and the last row as the final
coordinate times `lastRow k`. The defining identities of the chosen tests
then identify every Schwartz factor in the required formula.

The remaining calculation rewrites a sum over the product index type as
an iterated sum, distributes multiplication across the two finite sums,
and uses commutative ring arithmetic in each summand. No division by a
coefficient or test value is used, so empty families and zero tests present
no exception. Rank one is included through the supporting theorems.

This internal proof combines finite-function closure, root-coordinate
identities, compact support assembly and finite-sum algebra. It proves the
pointwise reduction only; it neither supplies the original coefficient
expansions nor asserts convergence, rationality or a common denominator.
