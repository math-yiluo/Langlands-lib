# Fourier covariance of actual supercuspidal cutoff coefficients

This internal derived helper uses the actual determinant-unit coefficient
cutoff from `SupercuspidalCutoffTests`, the raw full rectangular plus Fourier
transform against the nested product of the supplied additive Haar measure,
and the actual Jacquet coinvariant quotient. The field and representation
carrier have independent universes, the square rank is positive, and the
field topology is the supplied compatible p-adic topology.

Right translation of the representation vector by a determinant-norm-one
matrix equals right translation of the cutoff's matrix argument. The proof
checks determinant-unit matrices, other determinant shells, and singular
matrices separately. The published unimodular Fourier change of variables
then gives covariance of Fourier evaluation under right inverse transpose.

`supercuspidalCutoffFourierEvaluation` packages evaluation at a fixed matrix
as a complex linear functional in the representation vector, using the
existing raw Fourier linear map. This construction and the zero criterion
need no self-duality assumption on the supplied measure. If a subgroup has
zero Jacquet quotient, has determinant norm one, and fixes the Fourier
argument under right inverse transpose, covariance makes this functional
invariant. The actual universal lift through Jacquet coinvariants then
forces its value to be zero. No averaging or quotient measure is introduced.

Finally, every conjugate block unipotent radical has determinant norm one.
The proof uses the block-parabolic determinant formula and the radical's
identity Levi projection, then cancels the conjugating determinants.

The provenance is the preceding cutoff construction and existing Library
Fourier, block determinant, and coinvariant APIs. This module proves a
stabilizer criterion; it does not assert existence of a suitable proper
radical for every singular matrix, Fourier regularity of every cutoff,
nonzero operator realization, or the matrix functional equation.
