# The complex Godement kernel with additive Tate weights

The product of the multiplicative complex measures on the diagonal is
additive Lebesgue measure with the product of inverse squared norm
densities. The proof separates one coordinate and uses the product
measure identity to induct on the number of positions.

Multiplying the multiplicative kernel by this density cancels the first
normalized modulus power in each diagonal weight. At a zero diagonal
coordinate both the density-weighted kernel and the additive expression
vanish. At nonzero coordinates the character quotient gives the angular
Tate weight and its exponent. The resulting additive kernel factors as
the test with its compact weight times the product of the scalar Tate
weights. With a supplied s-finite compact-coordinate measure, the two
kernels have equivalent absolute integrability for their respective
measures and the same Bochner integral.

Combining this with the group-to-diagonal comparison gives
`complexGodementAdditiveDiagonal` for a continuous test and a smaller
standard vector given by a full list of characters. The theorem retains
the constant determined by the bi-invariant group Haar measure and the
unitary Haar measure, and it gives equivalent absolute integrability
before and after both changes of variables.

[Jacquet, *Archimedean Rankin–Selberg integrals*, §7.1, proof of Proposition 7.1, pp. 43–44](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf).

`integral_multiplicativeComplexDiagonal` gives the same product density for complex-valued integrals of functions of the diagonal alone.
