# Actual completed algebra charts for a split local pair

A center-preserving algebra equivalence from the actual local algebra
to the exchange pair determines an algebra equivalence at each actual
upper completion. `completedAlgebraEquivsOfSplitPair` gives those
equivalences in the order of the chosen place and its companion.

The published tensor comparison decomposes the actual local algebra
into the product of the algebras at the upper completions. Its two
coordinates agree with `toCompletedAlgebra`, as seen on pure tensors.
The center formula for `toCompletedAlgebra` and surjectivity of the
oriented center chart show that the product comparison carries the two
independent completed-field scalar actions to the corresponding scalar
actions of the exchange pair. Taking the scalar `1` in one coordinate
and `0` in the other gives the coordinate idempotents. Preservation of
these idempotents yields the two factor equivalences, and preservation
of the full scalar actions makes them algebra equivalences over their
respective completions.

`hasCompletedBrauerInvariant_of_splitPair` applies these charts to the
specified degree-`n` factor and its transported opposite. The signed
invariant is interpreted using the denominator equivalence and agrees
with the split-place clause of `UnitaryLocalProfileRealizationStatement`.
This is an internal comparison between local chart interfaces in the
Library for use in the realization direction of Clozel's split-place
profiles.

## Maximal-Witt charts from an upper matrix factor

`maxWittChartOfSplitCompletion` takes a matrix chart at the chosen upper
completion and a second-kind involution. In the actual product of the
completed factors, the involution swaps the two central idempotents.
The first component of the chart is the given matrix equivalence,
written over the base completion using the degree-one field chart.
The second component is obtained by applying the involution, taking
that first component, and applying the antidiagonal matrix adjoint
with trivial coefficient involution. The two anti-multiplicative maps
make the second component multiplicative. The involution recovers its
inverse from the first-factor chart.

The oriented center equivalence identifies matrices over the completed
center with pairs of matrices over the base completion. The two
components send the center to the two scalar matrices and exchange
under the antidiagonal adjoint. Recombining them gives the algebra
equivalence required by `IsQuasiSplitAt`, including both compatibilities.
`isQuasiSplitAt_of_zeroCompletedBrauerInvariant` obtains the initial
matrix chart from injectivity of the finite Brauer invariant and the
neutral-class splitting theorem. Scalar extension preserves the
central simple degree, so the matrix chart has the prescribed size.
