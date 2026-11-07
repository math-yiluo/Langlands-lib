# Real determinant twists of multisegment constituents

Author: Worker 1792. Module
`Langlands.Representation.Classification.MultisegmentConstituentRealTwistCompatibilityProof`.

`Langlands.Classification.multisegmentConstituentRealTwistCompatibility` proves
exactly the published proposition
`Langlands.Classification.MultisegmentConstituentRealTwistCompatibility.{uF, uV} F T`
of `Classification.MultisegmentConstituentCompatibilityStatement`, for arbitrary
`{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)` with
independent universes. It has no further hypotheses.

## Proof

The proposition is the special case `χ = |·|^s` of the proved
`multisegmentConstituentCharacterTwistCompatibility`. Take
`χ = realPowerCharacter T.normalizedAbsUnits s : F^× →* ℂ^×`. Its kernel contains
the open kernel of `normalizedAbsUnits` (`ker_le_realPowerCharacter_ker`), so it is
open (`Subgroup.isOpen_mono`, after installing the valued-field structure of `T`).
For this `χ` the composite `χ ∘ det` on `GL_k` is, by definition, the character
`T.determinantPowerCharacter k s = realPowerCharacter (T.determinantNorm k) s`, and
the character twist of a segment in the character statement is, by definition,
the real twist `Segment.twist s` (`supercuspidalClassRealPowerTwist` is the
supercuspidal class twist by `determinantPowerCharacter`). Hence the conclusion of
the character statement for `χ` is definitionally the conclusion of the real
statement, and the proof is that application.
