# Reduction of supercuspidal globalization to local occurrence

`GeneralLinearSupercuspidalPositiveRankOccurrenceStatement` asks for the
positive-rank summand, common integral-level vector and unramified determinant
twists with equivariant embeddings. The group scheme, measures defining the
cuspidal space, auxiliary place and two universes are those of
`GeneralLinearSupercuspidalGlobalizationStatement`.

`generalLinearSupercuspidalGlobalization_of_positiveRankOccurrence` supplies the
trace conclusion from the occurrence. The rank-zero branch uses the constant
line. In positive rank, the determinant valuation is locally constant around
the identity. Thus the unramified twist has open kernel and preserves
admissibility. Character twisting also preserves irreducibility.

The local affine-point homeomorphism pulls the prescribed matrix
representation and the test function back to the local point group. Its
inverse carries the specified matrix Haar measure to a Haar measure there.
The elementary algebraic change of variables identifies the local Hecke
operators and hence their finite-rank traces. Apply the per-summand
`IsotypicTrace.cuspidalIsotypicTraceFactorization_of_occurrence` with the
transported embedding and Haar measure. Its ordinary trace formula has one
functional for all the split tests. The change of variables converts it to
exactly the matrix-character identity in the globalization statement.
