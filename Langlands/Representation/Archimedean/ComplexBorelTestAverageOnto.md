# Surjectivity of complex Borel averaging onto smooth induced sections

For a multiplicative character \(\eta\) of the upper Borel
of \(\mathrm{GL}_n(\mathbb C)\), let \(F\) be a smooth function satisfying
\(F(bg)=\eta(b)F(g)\). Then a smooth matrix test \(\phi\) compactly
supported in the invertible matrices satisfies
\[
F(g)=\int_B \eta(b)\phi(g^{-1}b)\,d\mu(b).
\]
The proof uses a left Haar measure with the Borel measurable structure
and the second-countable topology on the upper triangular subgroup.

Choose a smooth nonnegative test \(\rho\), supported compactly in the
invertible matrices and strictly positive on the unitary subgroup.
Its untwisted inverse-argument average \(J\) is smooth and left Borel
invariant. It is positive at unitary arguments by positivity of the
integrand near the Borel identity. The upper triangular and unitary
factorization then makes \(J\) nonzero everywhere.

The function \(x\mapsto \rho(x)F(x^{-1})/J(x^{-1})\) on the group is
smooth and compactly supported. `matrixTestFunctionKernelEquiv` extends
it to a matrix test. Substituting this test into the weighted average
cancels \(\eta(b)\) with \(\eta(b^{-1})\), and the remaining integral
is \(J(g)\) times \(F(g)/J(g)\).

This is an internal consequence of the Library's complex triangular
factorization, smooth matrix test conversion, and weighted Borel
averaging. It supplies test functions for lifting a linear functional
on smooth induced sections.
