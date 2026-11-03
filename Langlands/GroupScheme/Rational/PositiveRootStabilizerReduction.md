# Positive-root stabilizers from explicit geometric statements

This internal reduction uses the actual character-valued relative roots,
normalizer quotient, and dynamic subgroup functors. It assumes the named
`RelativeRootSignInclusionsStatement`, `ParabolicDynamicStatement`,
`ParabolicSelfNormalizerStatement`, and `GenericCentralizerStatement`.
Their geometric assertions remain inputs.

`PositiveRootStabilizerReductionStatement` states the conditional implication
from those four assertions to triviality of the positive-root stabilizer for
every connected reductive group over an arbitrary field, every maximal split
torus, and every generic cocharacter. The theorem
`positiveRootStabilizerReduction` proves this implication by applying
`hasTrivialPositiveRootStabilizer_of_structural_statements`. This contribution
records the conditional statement and its supporting deductions.

For any group scheme over a base scheme, equality between a dynamic parabolic
and its conjugate places the conjugating base point in its normalizer functor.
The proof uses the dynamic conjugation equivalence on every test scheme and
every refinement. Its reverse implication supplies inverse conjugation as
required by the normalizer definition.

For a connected reductive group over a field, the affine dynamic construction
already supplies a closed representative of the parabolic on all test schemes.
The parabolic characterization statement makes this representative parabolic.
The self-normalization statement therefore identifies the normalizer functor
of the dynamic parabolic with that parabolic.

Let a rational normalizing point preserve the positive roots selected by a
generic integral cocharacter `ν`. The character action is precomposition by
the inverse torus automorphism. Consequently its pairing with `ν` equals
pairing the original character with `ν` postcomposed by that inverse
automorphism. The transformed cocharacter is generic because the normalizing
point permutes the actual roots. Genericity converts the equality of strict
positive supports into equality of nonnegative supports. The root-sign
inclusion statement then identifies the two dynamic parabolics.

The inverse normalizing point conjugates the cocharacter into that transformed
cocharacter, so it normalizes the dynamic parabolic. Subgroup inverse closure
gives the same membership for the original point. Self-normalization places
it in the parabolic. The published split-subtorus normalizer lemma then places
it in the dynamic centralizer of `ν`, which the generic-centralizer statement
identifies with the centralizer of the whole torus. Its class in the actual
quotient is the identity.

The final result is exactly `HasTrivialPositiveRootStabilizer i ν` under the
four statement inputs, connected reductivity, maximality of the split torus,
and genericity. It retains arbitrary fields and universes, nonreduced tests,
and empty relative-root sets. The deductions use published definitions and
proofs and elementary integer order reasoning; no new external theorem is
asserted. This file does not prove any of its four structural inputs, actual
reflection existence, or `RelativeRootSystemStatement`.
