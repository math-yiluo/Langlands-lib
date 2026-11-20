# Borel covariance of the ordinary complex adjacent-swap integral

`strictSwapFunction` evaluates the ordinary chart integral on the right
translate of a vector by a general group element. `integrable_strictSwapFunction`
gives absolute convergence for every such element on a smooth vector in the
strict convergence chamber. It uses preservation of the smooth principal
series under right translation and the bound in `ComplexStrictSwapIntegral`.

Right multiplication of the adjacent chart by an upper unipotent matrix
adds its simple-root entry to the chart coordinate, up to a left upper
unipotent factor. Before conjugation by the adjacent permutation, the
remaining unipotent factor has zero in the exchanged position. Left
unipotent invariance of the vector and translation invariance of Lebesgue
measure give the transformation law of the integral.

For a diagonal matrix with entries \(a_k\), the chart swaps the two diagonal
entries at \(i,j\) and scales the chart coordinate by \(a_j/a_i\). The
substitution in the complex plane contributes \(\lvert a_j/a_i\rvert^{-2}\).
The proof of `principalSeriesCharacter_swap_jacobian` shows that multiplying
by this Jacobian changes the two shifted exponents to those of the swapped
standard module. Iwasawa decomposition then extends the equality of the
Frobenius intertwiner and the chart integral from \(U(n)\) to every element of
\(\mathrm{GL}_n(\mathbb C)\), in `exists_strictSwapIntertwining_apply`.

This internal computation uses the Library's left Borel covariance and right
translation conventions for the complex rank-one case of the intertwining
integral in Wallach, *Real Reductive Groups I* (1988), Lemma 5.3.1 and §5.3.4,
printed pp. 144–145 and 147 (PDF pp. 164–165 and 167 of
`wallach-1988-real-reductive-groups-i`). The application is the archimedean
constituent step in Getz and Hahn, *An Introduction to Automorphic
Representations* (2024), Theorem 10.6.4, printed p. 286 (PDF p. 298 of
`getz-hahn-2024-automorphic-representations`).
