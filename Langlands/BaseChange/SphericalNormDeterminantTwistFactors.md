# Spherical standard factors after a common norm twist

`SphericalNormDeterminantTwistFactorsStatement` takes a finite abelian
Galois extension of p-adic fields with the relative module topology,
residue degree `f` and different exponent. The original lower and upper
objects are spherical, with the upper Satake multiset given by raising
the lower multiset to the `f`th power. The lower objects used for the
factors are determinant twists by the product of an arbitrary continuous
quasicharacter and each norm-trivial character. The upper object used for
the factors is twisted by the norm pullback of the same quasicharacter.

The standard pair choices use trivial rank-one partners and nontrivial
additive characters related by trace, with their self-dual measures.
The product of the certified lower Euler polynomials is the certified
upper Euler polynomial at `X^f`. The sum of the lower integer epsilon
exponents is `f` times the upper exponent.

The proof chooses ordered spherical presentations using the two Satake
multisets. The standard factor formula of a determinant-twisted spherical
representation expresses its Euler polynomial and epsilon exponent as
products and sums of Tate factors. For each lower Satake parameter, the
norm of the unramified rank-one inducing character is computed by the
relative order formula. `padicCharacterNormFactors` compares the resulting
rank-one twists with the upper inducing character. The products and sums
depend only on the upper Satake multiset, so the rank-one comparisons give
the comparison for the supplied upper presentation.

This is a derived extension of the spherical calculation in Arthur–Clozel,
Chapter 1, Lemma 6.13, printed p. 70 (PDF p. 84), literature ID
`arthur-clozel-1989-base-change`, SHA-256
`c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`.
