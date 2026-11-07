# Conditional arithmetic epsilon values of character pairs

This internal unit computes the full common-closure arithmetic pair epsilon
value for two actual continuous character lines. It retains an explicitly
supplied reciprocity family, an explicitly supplied assignment satisfying
`NonabelianSystem.IsSystem`, a finite intermediate field, a nontrivial unitary
additive character, any actual additive Haar measure, a supplied geometric
Frobenius and any complex spectral parameter. The field and representation
carrier universes are independent.

The definitions and deductions compose published constructions in
`CommonClosure`, `CommonClosureSpectral`, `CommonClosureWeilDeligne`,
`CommonClosureGamma`, `CharacterLine` and `ExactTensor`. They are internal
consequences of those constructions; no new original-literature assertion is
introduced.

The existing `CommonClosureSpectralAnalytic.fieldCharacterEquiv` descends a continuous character of the
actual fixing subgroup to its closed-commutator quotient and transports it along
the supplied reciprocity component to a continuous field character. Its two
inverse identities identify descent and the existing `weilCharacter` pullback.
The equivalence constructs no reciprocity family. This module reuses it and
`CommonClosureSpectralAnalytic.weilCharacter_fieldCharacterEquiv` from
`CommonClosureRankOneSpectral`, and adds the other inverse identity
`CommonClosure.fieldCharacterEquiv_weilCharacter`.

`virtualTwist_characterClass` specializes the existing exact continuous twist
formula: the spectral twist of a genuine character class is the class of the
spectral character times that character. Consequently
`conditionalDeligneValue_characterClass` applies the supplied system's rank-one
law to the descended product. Its right side is the actual complex-valued
`abelianEpsilonExpression` with the same additive character and measure.

`CommonClosureWeilDeligne.characterPair` is the zero-monodromy pair on the
universe-lifted complex character line, with the actual restricted norm
character. Its underlying representation is continuous, and its exact virtual
class is the existing character class. The actual tensor monodromy is zero
because both summands in `N ⊗ 1 + 1 ⊗ N'` vanish.

`characterPairTensorEquiv` first uses `tensorCharacterLineEquiv` to identify
the tensor with the twist of the first line by the second character, then uses
`twistCharacterLineEquiv` and commutativity of complex units to identify this
with the product-character line. The same equivalence commutes with monodromy,
since source and target monodromy are zero.

`conditionalEpsilonValue_characterPair` uses the published theorem that zero
monodromy makes the actual invariant-quotient determinant correction one.
`conditionalPairEpsilonValue_characterPair` transports the full epsilon value
along the actual tensor equivalence. Thus the resulting expression is the
abelian epsilon expression of the descent of
`CommonClosureSpectral.character F E s * (χ * η)`.
`conditionalPairEpsilonValue_of_equiv_characterPair` transports both tensor
legs from any actual continuous pairs genuinely equivalent to those lines.

These formulas are conditional on the displayed system and reciprocity data.
They prove no existence of reciprocity, a local-constant system or a self-dual
measure, and assert no automorphic epsilon comparison, JPSS identity or closed
local Langlands correspondence. The full measure-dependent Deligne convention
and the base-degree spectral character remain those of the imported definitions.
