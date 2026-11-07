# Pair L-factors of the actual rank-one correspondence

This internal derived module compares the actual JPSS pair L-factor and the
arithmetic pair L-factor for the rank-one correspondence along a supplied
geometric reciprocity candidate. It retains every prime, every p-adic field,
an independent parameter-carrier universe, and independent carrier universes
for the two supercuspidal outputs. Both continuous multiplicative characters
and their product may be ramified.

The exact character-pair certificate from `TateCharacterLFactor` transfers
through genuine representation equivalences on both members. Its polynomial
is `PadicAbelian.lPolynomial` of the product character, and it includes actual
compatible quotient-measure existence. Uniqueness against the constructed
quotient Haar measure identifies the existing selected `padicPairLPolynomial`
with this polynomial. Taking its reciprocal identifies `padicPairLFactor` with
the existing abelian rational L-factor. The same uniqueness gives the formula
for `genericPairLFactor` whenever the representatives have the displayed
genericity certificates. These selection formulas use the existing objects;
no alternative L-factor is introduced.

The lifted line defining `rankOneSupercuspidalObject` is genuinely equivalent
to the scalar character representation by `characterLineEquiv`. Applying the
representation-level certificate through these equivalences proves the
existing quotient relation `IsSupercuspidalPairLPolynomial` for the actual
rank-one character classes. Equal ranks select the first branch of the
published symmetric JPSS relation. The two lifted carriers are allowed to have
different universes. Uniqueness of the existing scalar-character class relation
then gives the same conclusion for any classes realizing these characters.

For actual rank-one Weil classes `σ` and `τ`, the published character
normalization theorem supplies continuous field characters along the given
reciprocity candidate. The specification of `rankOneReciprocityEquiv` identifies
its outputs with the corresponding actual supercuspidal character classes.
The polynomial of the product character therefore certifies the analytic pair.
The published theorem
`arithmeticPairLFactor_of_isRankOneWeilCharacter` computes the actual
zero-monodromy tensor-pair L-factor as the reciprocal of exactly that
polynomial, using the supplied geometric reciprocity property.

`RankOnePairLCompatibilityStatement F e` collects this separate pair-L
comparison for every additive character of the existing local character type,
every additive Haar measure and both actual rank-one Weil classes.
`rankOnePairLCompatibilityStatement` proves it under
`IsGeometricReciprocity F e`. No self-dual normalization or existence of a
self-dual measure is used or asserted. The final theorem applies the existing
equational characterization of rank-one compatibility to any two supplied
families satisfying it; its conclusion concerns only their rank-one values.

The provenance is internal: the exact scalar-to-JPSS normalization, equivalence
invariance, selected-polynomial uniqueness, genuine lifted character lines,
rank-one reciprocity bijection and arithmetic pair-L calculation are existing
constructions and theorems. This module does not prove existence of geometric
reciprocity, analytic epsilon compatibility, pair-factor compatibility in
higher rank, or the closed all-field supercuspidal correspondence.
