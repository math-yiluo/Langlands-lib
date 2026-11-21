# Reduction of two-place Harris parity normalization to auxiliary normalization

`Langlands.Global.Harris.proposition48ParityNormalizationReduction` proves
`Proposition48ParityNormalizationReductionStatement.{uF}`. It follows the
two-place normalization route in the [paired statement](HarrisProposition48ParityReductionStatement.md#two-place-normalization),
a derived step for the parity correction in Harris (1998), Proposition 4.8.

Given `Q.IsValidAtParity b`, the proof selects the conjuncts for
`Q.IsAuxiliaryValidAtParity b`. The auxiliary normalization hypothesis
supplies a correcting base character `ν` and a normalized auxiliary
component `χs`. It gives conjugate inversion and the required infinity
parity of `ν`, including its triviality when the parities agree.

The proof applies the finite-place transport hypothesis to `Q.P` and
`Q.χ`, with that same `ν`. This gives an actual primary component of
`Q.correctedCharacter ν`. The primary Weil twist equation is not needed:
the general-position clause is at `Q.Ps` and comes from the corrected
auxiliary validity.

Since `withCharacters` changes only the characters, normalized
reciprocity, the field hypotheses, both places' prime, compatibility and
uniqueness clauses, and both distinctness clauses are retained from the raw
datum. The corrected auxiliary validity supplies algebraicity at the rank
parity, relative regularity, conjugate inversion, and the auxiliary
component as well as general position. Together with the transported primary
component these give full validity of the corrected datum. Both normalization
and finite-place transport remain hypotheses of the reduction.
