# Arithmetic epsilon certificates of actual rank-one Weil classes

This internal unit connects the explicit common-closure character-pair epsilon
formula to the actual quotient classes and arithmetic certificate used by the
correspondence. It retains an explicitly supplied standalone reciprocity
candidate, a supplied common-closure reciprocity family and a supplied
nonabelian local-constant system. The field universe, parameter carrier
universe and system carrier universe are independent.

The construction is derived from the existing `ArithmeticFactors`,
`ArithmeticEpsilonDirectSum`, `RankOneReciprocityBijection`,
`UnramifiedReciprocityBridge` and `CommonClosureRankOneEpsilon` constructions.
No original-literature assertion is introduced.

`baseRestrictedWeilCharacter` restricts an actual continuous character of the
local Weil group to the bottom fixing subgroup by its continuous inclusion.
`rankOneBaseCharacterPairEquiv` identifies the restricted zero-monodromy
character line in the parameter universe with the character pair in the
system universe. Both genuine linear equivalences pass through the scalar
complex line. The published `zeroMonodromyCongr` preserves monodromy.

`isBaseRestriction_rankOneWeilCharacterClass` exhibits the actual lifted
character line as a representative of the specified rank-one quotient class
and uses this pair equivalence as its bottom restriction datum.
`IsBaseRestriction.nonempty_equiv_rankOneWeilCharacterClass` uses the published
`IsBaseRestriction.nonempty_equiv`: equality of genuine pair classes supplies
an actual pair equivalence to the same representative. Inverting that
equivalence and composing with the explicit line equivalence handles every
restriction datum, without choosing a special representative for the input.

`conditionalPairEpsilonValue_of_rankOneBaseRestriction` transports both actual
bottom pairs to their character lines and applies
`conditionalPairEpsilonValue_of_equiv_characterPair`. The result is the
abelian epsilon expression of the character descended through the supplied
common-closure family from the product of the spectral character and the two
restricted standalone Weil characters. It holds for every supplied additive
Haar measure and geometric Frobenius. The full invariant-quotient correction
is included by the imported formula.

`isArithmeticPairEpsilonFactor_rankOneWeilCharacterClass_iff` rewrites the
existing full arithmetic certificate. Its right side retains existence of a
transported nontrivial unitary additive character and a self-dual measure,
existence of an actual bottom geometric Frobenius, and the abelian epsilon
monomial identity for every admissible character and self-dual measure at
every complex spectral parameter. The forward implication tests the original
certificate on the explicit continuous character pairs. The reverse
implication provides those pairs for the certificate's existential clause
and uses the general restriction formula for its universally quantified
clause. The monomial uses the original base residue cardinality, scalar unit
and integer exponent.

The standalone and common-closure reciprocity data are not assumed compatible;
the result explicitly descends the restricted standalone Weil characters
through the displayed common-closure family. It does not identify that
descended character with a separately transported field character. It
constructs no reciprocity data, additive character, self-dual measure,
Frobenius or monomial constants, and proves no analytic epsilon comparison or
closed local Langlands correspondence.

The character descent uses the existing `CommonClosureSpectralAnalytic.fieldCharacterEquiv` and its inverse identity from `CommonClosureRankOneSpectral`.
