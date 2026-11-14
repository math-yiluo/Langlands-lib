# Rational characters and valuation kernels of a cocenter

This derived construction implements the character part of the cocenter reduction
in Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023), proof of
Lemma 11.5.2, printed p. 431, PDF p. 462. It is not a proof of the whole lemma.
The authors' November 2024 corrections leave this argument unchanged.

For any field `k`, a connected reductive `k`-group `G`, and an actual
`Cocenter k G`, `Cocenter.characterEquiv` is the additive equivalence
`X*(G/G_der)_k ≃ X*(G)_k` whose forward map is restriction along the
given quotient. The statement concerns the existing actual rational characters,
with no chosen character basis.

The proof identifies the scheme kernel of the quotient with the derived subgroup,
using the all-test kernel equality in `Cocenter.isQuotient`. The published derived
character annihilation theorem makes each character trivial on that kernel.
The quotient is flat and surjective by its definition and quasi-compact because
the source and target are affine over the field. `FpqcHomDescent.hom` therefore
descends the actual character, and its factorization law gives surjectivity of
character restriction. Scheme epimorphy of the quotient gives injectivity.

`Cocenter.characterValuationKernel_eq_comap` proves that the existing common
character-valuation kernel of `G` is the inverse image of that of the cocenter
under the actual quotient's point homomorphism. It works for any valuation into
any linearly ordered commutative group with zero. One inclusion is character
restriction; the other uses the established surjectivity of restriction.
Surjectivity of the quotient on `k`-points is neither assumed nor used.

The provenance is derived: KP uses the definition of `G(k)^1` at this step,
while this module spells out the required character descent and kernel equality
for the Library's group-scheme and valuation interfaces.
