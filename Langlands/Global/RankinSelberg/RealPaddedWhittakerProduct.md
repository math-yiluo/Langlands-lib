# Opposite real Whittaker forms on the smooth product

Take jointly continuous complex Banach representations of two positive
rank real general linear groups. On their genuine word-derivative
smooth spaces, take continuous complex-linear forms with real Whittaker
characters of opposite nonzero additive scales. The proposition
`RealPaddedWhittakerProductStatement` gives a continuous complex-linear
form on the genuine smooth part of the completed Banach projective
product for the two groups acting independently. Its value on a pure
smooth tensor is the product of the original values. Its covariance
under an arbitrary pair of upper unipotent matrices is the product of
the two Whittaker characters. In particular, it is invariant under a
common upper unipotent subgroup inserted into both leading blocks,
including when either embedding is at equal rank.

Use `smoothProjectiveProductFunctional` to extend the product. After
translation by a pair of upper unipotents, the two covariance identities
compute the extended form on pure tensors. Continuous forms agreeing there
agree on their complex span and therefore on the whole genuine smooth
space by `smoothProjectiveProductDensity`. Padding with identity preserves
the upper unipotent condition and leaves the sum of the adjacent upper
entries unchanged. The two resulting characters cancel because their
additive scales are opposite.

Jacquet defines the paired coefficient from the two Whittaker evaluations in §2, p. 8.
He uses the coefficient in the padded integrals on p. 105 and applies the compensating
subgroup on p. 106 in the proof of Lemma 14.1.
[H. Jacquet, *Archimedean Rankin–Selberg Integrals* (2009), author-posted edition](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf#page=8).

The registered source is `jacquet-2009-archimedean-rankin-selberg`, SHA-256
`7a11766eadf25fb7452ce7faa193469791796f572fc654c8fe90a8608bb46afe`.
