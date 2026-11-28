# Reversal of a Siegel chamber

`AdelicSiegelOppositeChamberStatement` gives the algebraic Siegel setup
for the negative of the supplied generic cocharacter of a connected
reductive group over a number field. It keeps the maximal split torus
and its derived split factor. Inversion of the positive torus point
identifies the two weak simple-root chambers at the same threshold
and gives the same value of the Siegel modulus.

The minimal parabolic and Levi structure for the negative cocharacter
comes from genericity. The derived and central split data already
belong to the original setup. Negating the characters carries positive
roots to the opposite positive roots and preserves indecomposability,
so it also carries simple roots to opposite simple roots. Evaluating
the opposite character at the inverse torus point preserves its
normalized absolute value. Opposite weights have equal multiplicities
by the relative root system, so the two products for the modulus agree.

The comparison permits use of the existing contraction and Haar-modulus
formulas for the opposite chamber. The positive-weight product is the
conjugation determinant in Delorme's Siegel coordinates.

Delorme, *On the spectral theorem of Langlands*, Advances in Mathematics
426 (2023), 109107, published PDF pp. 6–7, §2, the parabolic conjugation
determinant and (2.3)–(2.4).
