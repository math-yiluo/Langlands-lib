# Hermitian pairs in real standard parameters

Assume uniqueness for irreducible real standard modules that have positive induced weights. `realStandardHermitianPairDecomposition` groups the blocks of an irreducible, generic, infinitesimally unitary real standard module with positive induced weights into singleton unitary discrete blocks and pairs of opposite real determinant twists of the same unitary discrete block. The flattened grouping is a permutation of the input list. The pairs are ordered by positive twist first.

The Hermitian-dual parameter gives a second presentation of the same module. Normalizing its induced weights retains each parity or weight and each imaginary exponent, and negates each real exponent. The normalization identifies the same standard function space. The normalized intertwiner is bijective by irreducibility and injectivity, so the uniqueness premise identifies the reflected list with the original list up to permutation.

Induction on list length extracts either a singleton with zero real exponent or one occurrence of a block and one occurrence of its reflection. In each case the remaining list is again invariant under reflection up to permutation. Untwisting a pair to real exponent zero gives its common unitary discrete block.

The argument is a deduction from the Library's Hermitian-dual parameter construction and its uniqueness statement based on Knapp (1994), Theorem 1(c), p. 400 (PDF p. 410). Here the magnitude of a twist in a pair is unrestricted. Badulescu–Renard (2010), Theorem 8.2, p. 1131 (PDF p. 18), and Proposition 9.4, p. 1133 (PDF p. 20), give the classified unitary pairs with twist in the open interval `(0, 1/2)`.

## Hermitian-dual equivalence of a factor

`realHermitianInducingFactor_dualEquiv` gives a complex-linear equivalence from the compact-finite standard module of an irreducible, pairwise unlinked Hermitian factor to the compact-finite standard module of its Hermitian-dual list. The equivalence intertwines the compact and Lie actions, at the factor's total rank.

Real determinant twists preserve induced weights. The normalization calculation above therefore applies to each block of a Hermitian factor. Reflection fixes the singleton of exponent zero and exchanges the two opposite twists of a common block. Thus the normalized dual list is a permutation of the factor. Linkage is symmetric, so the normalized dual list is pairwise unlinked. `realUnlinkedStandardPermutation` gives an injective intertwiner from it to the factor. The equality of standard function spaces under normalization transports this map to the actual Hermitian-dual list. The source is nonzero by standard-module nontriviality. Irreducibility of the factor makes the map surjective, and `RealDiscretePresentation.isGKMap_symm` supplies the intertwining identities for the inverse.

This internal argument produces the Hermitian equivalence used in algebraic descent of positivity to inducing factors.
