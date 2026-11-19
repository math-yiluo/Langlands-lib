# Diagonal weights in the complex Godement integral

For each diagonal entry the column Jacobian contributes the inverse
normalized modulus to the power of its column index. The smaller induced
vector is evaluated at the inverse triangular factor, so its character and
Borel weight are evaluated at the inverse diagonal entry. The added
character and its determinant weight are evaluated at the diagonal entry
itself. Combining the three powers leaves one power of the normalized
modulus times the ratio of the two characters. For a full list of
inducing characters the resulting exponent at position `j` is
`u_n - u_j + 1` in the source's notation. The Lean expression uses the
Library's trivial character at positions beyond the end of a shorter list.

The pointwise identity follows from upper-Borel covariance of the smaller
vector and determinant multiplicativity. The proof adds the three
exponents at each position. The determinant of the unitary coordinate has
normalized modulus one, so its character factor stays with the compact
part of the integrand. The additive triangular entries give the remaining
argument of the Schwartz test.

[Jacquet, *Archimedean Rankin–Selberg integrals*, §7.1, proof of Proposition 7.1, p. 44](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf).
