# Permutations of Langlands-ordered standard modules

Two weakly decreasing lists of inducing blocks that are permutations of
one another can be aligned by adjacent swaps of blocks with equal real
exponent. To move the first block of the target list to the front of the
source list, remove one occurrence and use the permutation of the
remaining lists. Every preceding block has real exponent at least that
of the removed block by the source order and at most that exponent by
the target order. Each such block can therefore be exchanged with the
removed block. Induction then aligns the tails.

In the real case, equal real exponents imply the Mœglin data are unlinked
by `RealTiedScalarAssembly.areRealBlocksUnlinked_of_eq`. The real unlinked
swap theorem supplies an injective intertwiner, which is surjective by
`realSwapInjectiveIntertwinerSurjective`. In the complex case,
`ComplexTemperedSorted.not_linked_of_re_eq` gives the unlinkedness. The
rank-two irreducibility theorem and the unlinked swap reduction give a
bijective intertwiner. Composing these maps along the sequence of swaps
gives the comparison of the full standard modules.

For the real Mœglin-data comparison, each character datum is reconstructed
from its parity and exponent. Each nonzero discrete-series weight is
reconstructed using its absolute value, which gives the same standard
module by `RealInducedSwapArithmetic.standardModule_replace_induced`.
The expansion identity `realStandardModule_append_expand` replaces a
weight-zero block by its two character blocks with the same exponent.
The normalized lists preserve rank and order. The proof composes the
transport maps from the two standard-module equalities with the
intertwiner for the permuted normalized lists.

The real order used for the swaps is the weak decrease of the real
parts of the determinant exponents in Getz–Hahn (2024), (10.29)–(10.30),
printed p. 283 (PDF p. 295). The corresponding quotient permutation
assertion is in Theorem 10.6.1, printed p. 284 (PDF p. 296). Knapp
(1994), Theorem 1(c), printed p. 400 (PDF p. 410), gives the analogous
assertion with (2.5) printed using `Re(t_j)/n_j`. See the Library's
calculation of the positive chamber in
[IsobaricAutomorphicRepresentation, §2](../../Global/Factors/IsobaricAutomorphicRepresentation.md#2-the-langlands-order-of-archimedean-blocks).
The real parameter conventions are from Knapp, (3.2)–(3.4), printed
pp. 402–403 (PDF pp. 412–413). The complex comparison uses (4.3) and
corresponds to Theorem 4(c), printed p. 405 (PDF p. 415). The module
constructs intertwiners on the standard modules for use in the
Langlands quotient comparisons.
