# Quotient algebra for the actual Iwahori–Weyl group

This is an internal group-theoretic helper for the published
`IwahoriWeylExactSequenceStatement` and `IwahoriWeylChamberSplittingStatement`.
It is derived from the definitions in `IwahoriWeyl` and the first isomorphism
theorem. It does not prove either global statement on its own.

For the same actual data `P`, assuming the two normalities when the relevant
quotients require them, the kernel of `P.toComponents` equals `P.affinePart`.
The proof uses Mathlib's kernel formula for a quotient lift; the preimage of
`G(F)^0` in `N(F)` is exactly `P.normalizerZeroComponent` by definition.
Consequently the affine part is normal. The surjectivity criterion says
precisely that the actual normalizer meets every coset in `G(F)/G(F)^0`.

`exists_affinePart_equiv_of_action` constructs a group isomorphism to the affine
Weyl group from three intermediate facts about the restricted actual apartment
action: its values lie in that Weyl group, it is onto that group, and its
kernel is the actual `Z(F)^0`. The projection onto the affine part is onto,
and has the same kernel. The two first-isomorphism-theorem equivalences
therefore yield the comparison. The proof verifies its value on every
normalizer representative. These intermediate facts are hypotheses of this
helper, and remain proof obligations for the global target.

The general complement lemma shows that the restriction of a surjection to a
complement of its kernel is bijective. Injectivity follows from the trivial
intersection of the complementary subgroups. For surjectivity, decompose a
preimage as a kernel element times a complement element. Its converse obtains
that decomposition from the unique restricted preimage. Applied to the
component map, these give the chamber-stabilizer component bijection and its
converse without discarding any component.

The intended mathematical context is Kaletha–Prasad, *Bruhat–Tits Theory:
A New Approach* (2023), Theorem 7.8.1(1) and §7.8.2 (PDF pp. 303–304),
with the corrected Chapter 7 assumption AS5 from the authors' corrections
of 1 November 2024 (PDF p. 33). This module supplies only the elementary
quotient steps; it does not establish KP's action comparison in Theorem 7.5.3
or the affine-chamber transitivity of Lemma 1.3.17.
