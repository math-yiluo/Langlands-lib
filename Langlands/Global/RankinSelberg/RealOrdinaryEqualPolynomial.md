# Polynomial normalization of real ordinary character-list tests

`RealCharacterOrdinaryPolynomialStatement` is the polynomial conclusion
for real character lists at the two standard additive scales. It covers
every adjacent-rank ordinary test and every equal-rank test with a
standard polynomial Gaussian row. The normalizations use the specified
real pair factors and the supplied rank-correct quotient measures.

`realOrdinaryEqualPolynomialStep` uses the smaller adjacent-rank result
at the opposite additive parameter. The strong Godement chamber gives
the initial polynomial result. For a holomorphic path of upper exponents,
keep the upper compact profile fixed and continue its Jacquet value.
The locally uniform derivative bound gives a uniform toral gauge on a
parameter disk. The equal-rank family theorem yields joint holomorphy on
the disk and a common right half-plane. Multiplication by the entire pair
denominator gives a family whose polynomial fibers continue to parameter
one. The equality of Whittaker models at the indicated ranks and the
canonical range result transfer the conclusion to all exact tests.

The rank induction starts with `realRankOnePolynomial`. It alternates
`realOrdinaryAdjacentPolynomial` with `realOrdinaryEqualPolynomialStep`
at the two opposite parameters. This formalizes the polynomial recursion
for character lists in Jacquet, *Archimedean Rankin–Selberg Integrals*,
§8.4, Proposition 8.1, pp. 60–61.
