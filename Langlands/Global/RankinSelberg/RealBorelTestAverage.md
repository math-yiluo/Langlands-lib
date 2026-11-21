# Upper triangular averaging of real matrix tests

`Langlands.Global.RankinSelbergGlobal.RealBorelTestAverage.RealBorelTestAverageStatement`
starts with a smooth compactly supported complex-valued test on the open
set of invertible real matrices. Averaging its left upper triangular
translates against a right-invariant measure finite on compact sets,
with the inverse of a continuous character, gives a smooth function
with that character on its left upper triangular argument.

The proof lifts the support to the real group of units. For a compact
output set, the relevant upper triangular matrices lie in the product of
that lifted support and the inverse output set, intersected with the
closed upper triangular subgroup. This compact bound proves integrability
and lets the proof use a fixed compact integration set locally. Compact
parameter integration gives smoothness. The same derivative formula
shows that infinitesimal right multiplication commutes with averaging,
because the derivative test is supported in the original support.

Right invariance of the measure and multiplicativity of the character give
the inducing law. The companion lemmas give complex linearity and the
two translation identities for tests, with measure preservation required
for left translation. These internal results prepare the distribution
associated with a continuous principal-series functional.
