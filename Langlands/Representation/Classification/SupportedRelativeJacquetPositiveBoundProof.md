# Positive inner Jacquet multiplicity from the supported quotient

Worker 429 implements this internal adapter. Worker 435 identified the existing
quotient transport, second-adjointness and simple-map detection interfaces.
The theorem `Langlands.glSupportedRelativeJacquetPositiveBound` proves exactly
`Langlands.GLSupportedRelativeJacquetPositiveBoundStatement.{uF,uV,uW}`.
The field, fine carrier and coarse carrier universes remain independent.

Given the actual zero-parameter support quotient `q₀`, the proof applies
`refinedLeviRealTwist` to obtain the actual surjective map `qₜ` at the chosen
arbitrary real coarse parameter. Fine-twist regularity supplies irreducibility
and admissibility of the actual refined fine twist. The published
real-twist preservation lemmas also give irreducibility and admissibility of
the coarse representation. Its irreducibility makes its carrier nontrivial,
so surjectivity of `qₜ` shows that `qₜ` is nonzero.

The refined clause of `Parabolic.normalizedSecondAdjointness` sends `qₜ` to
a map from the fine twist into the inner normalized opposite Jacquet module.
Its linear equivalence is injective and preserves zero, so this adjoint map
is nonzero. Independently, `glRelativeJacquetEmbedding` uses the supplied
actual ambient count `M` to construct an actual inner count `m ≤ M`.
Finally, `SimpleMapMultiplicityDetectionProof.positive_of_simple_map` uses
the irreducible fine twist and the nonzero adjoint map to prove `0 < m`.

Every count is the published actual composition-series multiplicity.
The ambient count is an explicit premise: this theorem does not construct
its finite series. It asserts neither equality of the two counts nor a head
of outer induction. The proof uses no unitary, tempered, genericity,
selected-branch, continuation or analytic-criterion premise. It imports the
published lower results by their Lean names and leaves the stronger supported
regular comparison and its remaining finite-length and head obligations open.
