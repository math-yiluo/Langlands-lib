# Centered square-integrability of special quotients

Author: Worker 1765.

`Langlands.Classification.segmentCenteredSpecialSquareIntegrability` proves
the unchanged Library proposition
`Langlands.Classification.SegmentCenteredSpecialSquareIntegrability.{uF,uV}
F T`, with independent field and carrier parameters. It concerns the supplied
quotient and its original carrier at universe `max uF uV`.

The premise supplies an actual unitarizable supercuspidal representative of the
base of the increasing segment. For every supplied irreducible quotient of
that segment induction, the theorem proves analytic square-integrability and
unitarizability of its twist by `ν^(-(m-1)/2)`. It adds no central-character,
classification or factor hypothesis.

## Implemented proof

The published `unitarizableCentralCharacter` extracts a unitary character of
the full center from the base representation's admissibility, irreducibility
and invariant positive form. Restricting it to scalar matrices gives a scalar
character `ω` of norm one.

`segmentConstituentCentralCharacter` gives the scalar character of the actual
quotient as `ω^m` times the determinant character with exponent `(m-1)/2`.
`hasScalarCharacter_twist` gives the character after the negative midpoint
twist. The character identity `realPowerCharacter_neg` cancels the two
determinant characters exactly, leaving `ω^m`, still of norm one.

The quotient is admissible by `cuspidalEmbedding`; admissibility and
irreducibility survive the actual twist. Irreducibility also supplies a
nontrivial carrier. `glSquareIntegrableCentralCharacter` turns the computed
norm-one scalar action into a unitary character of the full center.
The published essential square-integrability theorem for special quotients,
and its invariance under real twists, apply to this same representation.
`isSquareIntegrable_of_essential_of_unitaryCentralCharacter` then removes
the normalizing real twist and gives the full all-Haar analytic predicate.
Finally, `glSquareIntegrableUnitarity` constructs an invariant positive
definite Hermitian form on the centered quotient's original carrier.

## Provenance and scope

This is an internal derivation from the named Library proofs. The scalar
cancellation is the derivation explained for the fifth clause in
`SegmentSquareIntegrabilityStatement.md`. No additional assertion from the
literature is used here, and the imported statements retain their documented
source conventions.

The increasing segment remains uncentered; the twist is applied to its supplied
quotient action. The theorem does not construct unitary-generic exhaustion,
identify segment lengths, or prove the associated-pair induction theorem.
