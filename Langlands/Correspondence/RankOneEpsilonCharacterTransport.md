# Bottom-field characters in the rank-one arithmetic epsilon formula

Worker 1555 derives this internal transport from the actual field equivalence
`IntermediateField.botEquiv`, canonical p-adic topology, continuous character
transport and the existing arithmetic epsilon reduction. No external source
assertion is added.

`baseFieldPadicEquiv` upgrades the existing equivalence from the bottom
intermediate field to the base field to an equivalence over the specified
`Padic p`. Its commutation with the scalar map follows from the original
base-field algebra equivalence. `baseFieldUnitsEquiv` takes its map on units.
The published isometry theorem for p-adic algebra embeddings proves continuity
in both directions for the canonical topologies.

`baseFieldCharacterEquiv` transports each actual continuous quasicharacter
to the bottom field by composing with this units equivalence. The inverse
is the inverse pullback in the existing continuous character transport.
The evaluation formula and preservation of pointwise products are definitional.

With explicit `IsBaseReciprocity F e eC`,
`IsBaseReciprocity.units_eq` gives equality of the transported common-closure
reciprocity unit and the standalone reciprocity unit. Equality of their field
values is exactly the compatibility hypothesis, and unit extensionality
recovers equality of units.
`weilCharacter_baseFieldCharacterEquiv` applies the quasicharacter to that
equality. Thus the common-closure Weil pullback of the transported field
character is the restriction of the standalone Weil pullback.
`fieldCharacterEquiv_baseRestrictedWeilCharacter` applies the existing inverse
identity to recover the transported original field character.

`fieldCharacterEquiv_mul` proves preservation of products by applying the
injective inverse Weil pullback. Pullback commutes definitionally with products,
and the inverse identities finish the equality.
`fieldCharacterEquiv_rankOneSpectralProduct` then splits the descended
spectral product into the descended spectral character times the transported
product of the two original quasicharacters.

`conditionalPairEpsilonValue_of_compatible_rankOneBaseRestriction` rewrites
the existing full pair epsilon formula with this product identity. The input
pairs are arbitrary continuous actual bottom restrictions of the specified
rank-one Weil quotient classes, with independent parameter and system carrier
universes. The supplied geometric Frobenius, additive character and arbitrary
Haar measure are unchanged, including the full invariant-quotient correction
already handled by the imported formula.

`isArithmeticPairEpsilonFactor_compatible_rankOneWeilCharacterClass_iff`
applies the same rewrite to the existing arithmetic-certificate equivalence.
It retains existence of a transported nontrivial unitary additive character
and self-dual Haar measure, existence of a bottom geometric Frobenius, and
the monomial identity for every transported character, self-dual measure and
complex spectral parameter. The monomial still uses the original base
residue cardinality, complex unit and integer exponent. The proof rewrites
the descended spectral product under the existing universal quantifiers.

The standalone candidate and common-closure family are supplied and their
compatibility is an explicit hypothesis. No normalization or existence of
reciprocity is concluded. In particular, the descended spectral character is
not identified with a normalized absolute-value power. This construction
asserts no analytic epsilon comparison or closed local Langlands correspondence.

The character descent uses the existing `CommonClosureSpectralAnalytic.fieldCharacterEquiv` and its inverse identity from `CommonClosureRankOneSpectral`.
