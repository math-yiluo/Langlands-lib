# Base case and nonempty cuts for ample Euler positivity

`EulerPositivityPreparationStatement` groups two preparations for the
dimension induction proving positivity of an ample Euler polynomial.
It ranges over every field in an arbitrary universe and an actual scheme
over its spectrum.

For an actual module sheaf with finite cohomology and finite closed stalk
support, its Euler characteristic is the dimension of its zeroth actual
derived cohomology. This integer is strictly positive exactly when the
sheaf is nonzero. Finite cohomology is a hypothesis here, so this assertion
does not supply proper coherent finiteness for new coefficient sheaves.
The support condition is the published `HasFiniteClosedSupport`, defined
using the underlying abelian stalks.

The second assertion concerns a proper field scheme with strictly positive
topological Krull dimension. Such a scheme is not affine. For each ample
line bundle and each point it provides a positive tensor-power section
whose affine generation open contains the point and has a nonempty
complement. The assertion uses the published section generation locus and
ampleness predicate. It does not construct a closed subscheme on the
complement, assert that the section is regular, or identify a divisor's
dimension.

This is derived preparation for the proof in the registered source
`stacks-numerical-intersections-finite-locally-free-rank-2026-10-31`,
file `0BEL.html`, Lemma 33.45.9 and its proof. That proof starts with the
zero-dimensional cohomological base case and then chooses a section with
affine generation open, observing that proper positive-dimensional schemes
cannot be affine and hence that the vanishing set is nonempty.

The first assertion is derived from the published
`FiniteClosedSupportCohomologyStatement` and
`EulerCharacteristicBasicStatement`: higher cohomology vanishes, global
sections detect the zero sheaf, and finite dimensionality detects a
nonzero vector space by positive dimension. The nonaffineness assertion
uses proper affine implies finite; a scheme finite over a field is locally
Artinian, hence has discrete topology and dimension at most zero.
No polynomial construction or positivity of its leading coefficient is
assumed or asserted in this preparation.
