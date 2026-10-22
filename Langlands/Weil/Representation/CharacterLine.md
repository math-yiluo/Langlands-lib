# Continuous character lines in arbitrary carrier universes

Author: Worker 20.

This is an internal construction on the published finite representation,
scalar twist, continuity, and exact virtual representation interfaces. It
provides the rank-one input needed by arithmetic local-constant systems without
restricting their representation carrier universe to `Type 0`.

For a group `G : Type uG` and a homomorphism `χ : G →* ℂˣ`,
`FiniteRepresentation.characterLine χ` is the existing scalar twist of the
trivial representation on `ULift.{uV} ℂ`. Its action is precisely
`v ↦ (χ(g) : ℂ) • v`. This is an actual finite-dimensional representation,
not a new abstract parameter type. The complex coefficient field retains its
usual universe and topology; only the carrier is lifted.

`characterLineEquiv` uses `ULift.moduleEquiv` to identify this representation
with the published `Langlands.characterRepresentation χ` on `ℂ`. It is an
invertible intertwiner, and its rank consequence is proved using invariance
of finite dimension and `Module.finrank_self`. `twistCharacterLineEquiv`
identifies a twist by `χ` of the line for `η` with the line for `χ * η`,
using the published equality of successive scalar twists.

For a continuous character, `characterLine_isContinuous` proves the published
`FiniteRepresentation.IsContinuous` predicate. The proof composes the
continuous scalar-valued character with `z ↦ z • id` in the module topology
on the finite-dimensional complex endomorphism space.
`continuousCharacterLine` bundles this certificate with the same representation.
No topology on `G` beyond the one supplied to its continuous character is needed.

`ExactGrothendieckGroup.characterClass` inserts that actual continuous
representation into the existing quotient by genuine short exact sequence
relations. Its virtual degree is proved to be one.
`continuousTwist_characterClass` proves compatibility with the existing
continuous-character automorphism of that quotient, by applying the actual
intertwining equivalence above. This assertion is about scalar twisting;
it does not assert that character multiplication becomes addition in the
Grothendieck group.

## Provenance and scope

The mathematical content is derived from the published constructions in
`Langlands.Representation.Twist.Definitions`,
`Langlands.VirtualRepresentation.ExactTwist`, and
`Langlands.Weil.Representation.Predicates`, and Mathlib's `ULift.moduleEquiv`.
The continuity proof uses the same scalar-operator argument as the published
archimedean character construction, now in every carrier universe.
No unpublished draft is reused. There is no classification theorem for all
rank-one representations, local reciprocity theorem, or epsilon-system
existence assertion in this module.

