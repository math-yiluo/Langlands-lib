# Proof of the compact root-coordinate expansion

`Langlands.RankinSelberg.equalRankCompactRootExpansion` proves the conditional
`EqualRankCompactRootExpansionStatement` for independent field and
representation universes.

First, `equalRankRootExpansion` supplies the fixed finite family `η` and its
continuity and finite-dimensional translation-span properties from the two
assumed coefficient expansions. This happens before introducing the
functionals, coefficient-model vectors and Schwartz row test.

For each such choice of test data,
`equalRankNormalizedCompactIntegration` supplies compact representatives,
nonnegative real coefficients of sum one, and exact integral and absolute
integral formulas, uniformly in the group argument and spectral parameter.
At each of the finitely many representatives, the root expansion supplies
a Schwartz family `Ψ`. All these choices precede the root tuple and spectral
parameter.

For a fixed root tuple `a` and parameter `s`, `rootSpectralWeight` identifies
the determinant weight at each representative with the common explicit
spectral product. Its integral-subgroup clause supplies the determinant norm
one hypothesis. The proof rearranges the scalar products, applies the chosen
root expansion, and distributes the spectral factor over the finite sum.
This identifies the original integrand times the inverse-modulus factor
with the corresponding inner sum `S_t` at every representative.

The compact-integrability assertion follows by multiplication by the constant
inverse-modulus factor. For the complex integral, `integral_mul_const` and
finite-sum distributivity give the claimed formula. For the absolute
integral, multiplicativity of the extended norm and `lintegral_mul_const'`
move the finite extended norm of that constant outside the integral.
The existing absolute compact-average formula and the representative
identities then give the sum of weighted norms of `S_t`.

No norm is moved inside an inner sum. No coefficient, test value or functional
is cancelled or assumed nonzero. The result concerns compact integration;
the coefficient-expansion assumptions and subsequent torus and quotient
analytic steps retain their separate roles.
