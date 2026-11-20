# Hermitian pairs in real standard parameters

Assume uniqueness for irreducible real standard modules that have positive induced weights. `realStandardHermitianPairDecomposition` groups the blocks of an irreducible, generic, infinitesimally unitary real standard module with positive induced weights into singleton unitary discrete blocks and pairs of opposite real determinant twists of the same unitary discrete block. The flattened grouping is a permutation of the input list. The pairs are ordered by positive twist first.

The Hermitian-dual parameter gives a second presentation of the same module. Normalizing its induced weights retains each parity or weight and each imaginary exponent, and negates each real exponent. The normalization identifies the same standard function space. The normalized intertwiner is bijective by irreducibility and injectivity, so the uniqueness premise identifies the reflected list with the original list up to permutation.

Induction on list length extracts either a singleton with zero real exponent or one occurrence of a block and one occurrence of its reflection. In each case the remaining list is again invariant under reflection up to permutation. Untwisting a pair to real exponent zero gives its common unitary discrete block.

The argument is a deduction from the Library's Hermitian-dual parameter construction and its uniqueness statement based on Knapp (1994), Theorem 1(c), p. 400 (PDF p. 410). Here the magnitude of a twist in a pair is unrestricted. Badulescu–Renard (2010), Theorem 8.2, p. 1131 (PDF p. 18), and Proposition 9.4, p. 1133 (PDF p. 20), give the classified unitary pairs with twist in the open interval `(0, 1/2)`.
