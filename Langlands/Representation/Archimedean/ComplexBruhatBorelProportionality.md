# Proportional covariant distributions on the longest complex Bruhat cell

Consider two complex distributions on an open matrix set containing
the longest complex Bruhat cell. Both have the same continuous
multiplicative covariance character for pullback by the upper
unipotent times upper Borel action. If the first distribution is
nonzero on some test with topological support in the cell, the
restrictions of the two distributions to such tests are proportional.
The proof uses left Haar measure on the actual product group with
its second-countable topology and Borel measurable structure.

Fix a reference test of nonzero first evaluation and any other test
supported in the cell. Choose one smooth nonnegative window supported
compactly in the cell and positive on both test supports. Compact
transport of the supports gives compact parameter support for the
translated products. Their smooth integral gives a denominator
strictly positive on both test supports, because the integrand at
the group identity is positive. Dividing by it expresses each test
as an integral against the common window.

The proof adapts the compact-family averaging in
`LongestBruhatCellInvariance`. Covariance moves this integral through
each distribution, expressing its value by evaluation on the window
times a weighted orbit average with the given character. Each weighted
average transforms by that character, and the cell is a single orbit
by `complexLongestBruhatBorelChart`. The weighted average of the
reference test therefore has nonzero value at the long Weyl
representative. The ratio of the two averages at that point gives a
pointwise proportionality after applying the common window. Evaluating
both distributions shows that the proportionality between the
distributions is fixed by the original reference test.

This is an internal consequence of the published compact-family
integration and complex longest-cell coordinates. The result concerns
tests supported on the longest cell.
