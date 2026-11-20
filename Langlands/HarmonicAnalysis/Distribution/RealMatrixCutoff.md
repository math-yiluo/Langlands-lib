# Determinant cutoff from real invertible matrices to all matrices

Real smooth tests and complex-valued distributions on the entire
real square matrix space use Mathlib's test function topology.
Conjugation by an invertible real matrix and ordinary transpose
act by pullback on tests.

A smooth function of the determinant whose scalar support avoids zero
multiplies each full-space test into a test on the open invertible
matrices. The map is continuous and commutes with both pullbacks,
since determinant is invariant under both matrix operations.
Precomposing a distribution on the invertible matrices with this
map extends the localized distribution to all matrices and preserves
conjugation invariance.

For each test on the open invertible matrices its compact support
has compact determinant image away from zero. A smooth scalar cutoff
supported away from zero can equal one on this image. The chosen
cutoff then recovers the test from its inclusion into the full-space
test functions. This gives the implication from full-space transpose
invariance to the open-group distribution statement. The implication
is an internal localization argument and uses the full-space assertion
as its premise.
