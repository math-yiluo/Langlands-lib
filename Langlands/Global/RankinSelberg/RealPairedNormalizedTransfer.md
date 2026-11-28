# Entire normalization after real paired rank transfer

`RealPairedNormalizedTransferStatement` takes a finite comparison from a
smaller common rank to a larger terminal rank for a genuine smooth
paired form. For each allowed terminal vector and row choice, assume
absolute integrability on a right half-plane and an entire
`OrdinaryIntegralNormalization` by one supplied factor. Then each
smaller integral at determinant exponent `s` minus the rank gap has
an entire normalization by that same factor, as a function of `s`.
Its value multiplied by the positive measure scalar is the finite
sum of the chosen terminal normalized functions at every `s`.

The finite rank comparison chooses the vectors and row tests before
`s`. A larger common threshold ensures absolute integrability and the
right-half-plane normalization identity for every term. Multiplying the
finite sum of the terminal normalized functions by the reciprocal
comparison scalar gives an entire function. The integral comparison and
factorization of the common factor through the finite sum verify its
normalization on that half-plane.

`normalized_lower_mem` assumes in addition that the factor is nonzero
on a right half-plane. Uniqueness then puts every normalization of a
smaller integral in any complex linear subspace containing all terminal
normalized values. In particular, if every terminal normalized function
vanishes at a given point, the smaller normalized value vanishes there.

The pairing and finite rank comparison are the ones in Lemma 14.1,
pp. 105–107. The use of their complex linear span in the ordinary local
induction is in Proposition 14.3 and §14.3, pp. 104–108 of the author-posted
edition.
[H. Jacquet, *Archimedean Rankin–Selberg Integrals* (2009)](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf#page=104).

The registered source is `jacquet-2009-archimedean-rankin-selberg`, SHA-256
`7a11766eadf25fb7452ce7faa193469791796f572fc654c8fe90a8608bb46afe`.
