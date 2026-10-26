# Unitary central characters of unitarizable representations

`Langlands.unitarizableCentralCharacter.{uG,uV}` proves the exact published
`Langlands.UnitarizableCentralCharacterStatement.{uG,uV}`. The group and
carrier universes remain independent. The hypotheses are exactly an arbitrary
topological group, an actual complex representation, admissibility,
irreducibility and the existence of an invariant positive definite Hermitian
form. The conclusion is the existing full-center `UnitaryCentralCharacter`
datum, with its actual character, open kernel, norm-one values and scalar action.

The proof installs irreducibility and derives a nontrivial carrier using the
simple-module instance for the representation's monoid-algebra module. Choose
a nonzero vector v and an invariant positive form b from unitarizability.
The published `Langlands.admissibleSchur_centralCharacter` supplies a locally
constant character χ from the full center to complex units and its scalar
action on every vector.

For each central z, definiteness gives b(v,v) ≠ 0. Invariance and the scalar
action give

`conj(χ(z)) * χ(z) * b(v,v) = b(v,v)`.

The implementation uses the form's inner-product core to expand both scalar
arguments, then cancels the nonzero self-pairing. Taking complex norms gives
`‖χ(z)‖ * ‖χ(z)‖ = 1`; nonnegativity forces `‖χ(z)‖ = 1`.
The character's kernel is its fiber over 1, which is open by local constancy.
These data assemble the existing structure directly. No carrier norm or
topology, finite dimension, chosen input form, or central-action hypothesis is
introduced.

This is an internal derivation from published Library interfaces and Mathlib's
inner-product core identities, rather than a transcription of an external
literature theorem. The scalar cancellation is the same elementary argument
used in `Langlands.Classification.chosenUnitarySquareIntegrability`, now applied
to the general Schur character. The proof does not use that GL-specific result
or assume its hypotheses. The statement and all imported pairs are unchanged.
This theorem alone supplies no GL exponent rigidity, Jacquet comparison,
induction duality or irreducible-head result.
