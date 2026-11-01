# First nonpositive run with ordered upper endpoints

This module defines the proposition
`Langlands.Classification.OrderedRunFirstNonpositive`. It is a statement
only. It supplies no proof of the arithmetic assertion or of a classification
theorem.

The data are a positive number `k` of positions, positive natural lengths
`m i`, and real numbers `a i,b i` at each position `i : Fin k`. The upper
numbers `a` are nondecreasing. The hypothesis is

`sum_i (m i : Real) * (a i + b i) <= 0`.

The conclusion gives a position `i` whose endpoint sum is nonpositive. Every
earlier position `j < i` has positive endpoint sum, strictly larger lower
number `b j > b i`, and upper number `a j <= a i`. If `k > 1`, the selected
length `m i` is strictly less than the total length.

The endpoint ordering of each individual pair, integrality, and a formula
relating `m i` to the endpoint difference are unnecessary for this arithmetic
assertion and are not hypotheses. When the pairs really are interval
endpoints, the two inequalities say that the selected interval contains
every earlier interval. Repeated or equal upper endpoints are allowed.
The case `k = 1` is included; only the final strict length conclusion is then
conditional. Zero lengths are excluded.

## Provenance and intended use

This is a derived elementary finite-sum statement. It isolates the numerical
step in Jantzen (2000), Theorem 2.3.1, printed p.549 / PDF p.11, after a
decomposition into descending consecutive runs with nondecreasing upper
endpoints has already been established. The registered source is
`jantzen-2000-square-integrable-classical-i`, SHA256
`539eee93dd339c42bf6d065bbb1969ab0e2c6c54699c5b4447a2166a3ddf9428`.
The original chooses the first run with `a j <= -b j` and compares its
endpoints with the preceding positive runs. It does not state this abstract
weighted proposition verbatim.

For an actual descending consecutive run of length `m`, the sum of its real
exponents is `m * (a+b) / 2`. Therefore a nonpositive total exponent sum
motivates the displayed weighted hypothesis, after multiplication by the
positive constant two. This module does not prove that arithmetic-series
identity or supply any actual run decomposition.

The expected elementary proof first rules out positivity of all endpoint
sums, selects the least nonpositive position, and compares endpoints using
monotonicity of `a`. Positivity of a second length gives the final strict
bound. These are plans for a separate exact proof, not proof claims here.

In the intended representation-theoretic application, separate results must
produce the runs, prove the total-weight hypothesis, commute contained
special segments while retaining every outside factor, and realize the
moved run as an actual Jacquet occurrence to which a strict Casselman
inequality applies. The proposition assumes and concludes none of those
results. It uses only Mathlib arithmetic and finite ordered sets; there are
no representation objects, analytic predicates, universes of coefficient
modules, or classification inputs.
