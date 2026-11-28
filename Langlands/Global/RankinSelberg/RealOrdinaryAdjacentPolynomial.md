# Polynomial normalization of real adjacent-rank ordinary tests

`RealOrdinaryAdjacentPolynomialStatement` derives polynomiality of all
ordinary adjacent-rank tests of real character lists from polynomiality
of the smaller equal-rank tests of character lists with standard Gaussian
rows. The additive scale has absolute value one. The normalization uses
the prescribed real pair factor for the original character lists and the
supplied compatible quotient measure.

In the strong Godement chamber this is
`realAdjacentPolynomialChamber`. For a holomorphic path of upper
exponents, extend the fixed compact profile to standard sections along
the path. The unnormalized quotient integral is jointly holomorphic on
the parameter disk and a common right half-plane, and the pair
denominator is jointly entire. Multiplying by the denominator gives the
normalized family. The identity theorem extends the initial polynomial
identities to the common half-plane. `polynomialFiberContinuation` then
propagates polynomiality to parameter one. Dividing by the pair
denominator where it is nonzero gives the desired normalization. The
canonical range covers every exact test of the character lists.

This implements the adjacent-rank step of Jacquet, *Archimedean
Rankin–Selberg Integrals*, §8.4, Proposition 8.1, pp. 60–61, using the
common half-plane for canonical real Jacquet families and continuation
of their polynomial fibers.
