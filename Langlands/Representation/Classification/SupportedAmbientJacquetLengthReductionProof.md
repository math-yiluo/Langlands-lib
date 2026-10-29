# Supported ambient Jacquet finite-series reduction

The theorem `Langlands.glSupportedAmbientJacquetLengthReduction` proves the
Library proposition
`Langlands.GLSupportedAmbientJacquetLengthReductionStatement.{uF,uV,uW}`.
This is an internal composition of published Library results. The exact standard
cuspidal induction length proposition at the given positive rank remains an
explicit premise throughout.

The proof sets `α` to the actual flattened fine real twist with exponent
`-v₀ k + t ((B.flattenBlockEquiv S).symm k).1`.
Published twist invariance gives its irreducibility and cuspidality.
Applying the supplied exact `CuspidalInductionLengthTheorem` to `α` gives
finite length of `RelativeRecovery.fineAmbientInduced`.

The proof applies the published `fineAmbientQuotientTransport` to the
specified zero-parameter fine-support surjection and the identity quotient
of the outer induction `I` of `πt`. It produces an actual surjection from
the fine ambient induction onto `I`; finite length descends through it.
This reuses the existing real-twist quotient transport, surjectivity of
normalized induction maps and actual induction in stages.

Twist invariance and normalized induction admissibility show that `I` is
admissible. Finite length gives finite generation. The published
`Parabolic.oppositeJacquetFiniteLength` therefore applies to its opposite
Jacquet module for `B.flatten S`. The actual flattened opposite comparison
identifies that module with the ambient Jacquet module pulled back along
the constructed flattened Levi equivalence. Finite length transports first
through that equivalence of representations and then through the surjective
group equivalence.

Finally `MultiplicityAdditivityProof.exists_series` constructs an actual
finite composition series of the ambient Jacquet module. Its
`factorMultiplicity τ` is the required natural number, with the same series
as witness. The proof keeps the field, fine carrier and coarse carrier
universes independent and gives no positivity or head conclusion.
