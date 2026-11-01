# The actual coarse twist belongs to its real block

Author: Worker 526. The namespace is
`Langlands.TemperedCoarseRealBlock`. This internal consequence of analytic
temperedness retains independent field and coarse-carrier universes.

`realBlockEqTop` proves that the entire actual real twist of a tempered
coarse representation belongs to its real central block at
`size k * t k`. It imposes no irreducibility, support or nonzero-carrier
hypothesis and allows every real coarse vector.

Haar-measure existence on the actual Levi central quotient lets the proof
extract the unitary full central character contained in the analytic
tempered predicate. Restrict that character along `blockScalarToCenter`
and multiply by the restriction of the actual real determinant character.
This product acts by scalars on the twisted representation. The published
block-scalar determinant formula and unitarity give its real coordinates.

`InnerInducedCoarseScalar.realBlockEqTopOfScalar` then transports this
scalar character to the full centre, obtains its open kernel from
smoothness when the carrier is nontrivial, and handles the zero carrier
separately. The implementation uses the actual twist and the analytic
central-character and admissibility definitions. It establishes the
source block property used in quotient extraction, without an assumption
about the central action of any induced or quotient Jacquet module.
