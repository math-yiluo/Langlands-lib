# Covering unequal-rank normalized tests with strip growth

`HasCoveringUnequalNormalizedGrowthTests` requires a family of standard-outside ordinary unequal-rank tests whose entire normalized values cover the complex plane. It also requires a member whose normalized value is nonzero somewhere and has exponential strip growth. The larger rank is the first one.

`hasCoveringUnequalNormalizedGrowthTests_of_local` gives the family at the specified real and complex parameters and finite Euler factor choice. The two cuspidal realizations are trivial on the split centre and the specified presentations have irreducible admissible finite components. The retained finite set includes both exceptional sets and the finite additive conductor support of the nontrivial unitary adelic character trivial on the diagonal number field. Its canonical nontrivial finite components and their self-dual Haar measures are supplied. The archimedean premises are the opposite-character slice model comparisons with the specified ranges, pointwise normalized generation, and growth of the ordinary normalized values. For each spectral point choose normalized local tests nonzero at that point. Prescribe the finite coefficient and reference vectors, use the chosen infinite Whittaker functions in the two pure tensors, and apply finite separation to get the product of ordinary test kernels. Integration over the semilocal quotient gives the product of local normalized functions times a fixed nonzero scalar. The normalization multiplied by the specified archimedean and retained finite factors agrees with the partial integral on a right half-plane. The finite values are bounded on strips, so the explicit product proves exponential strip growth for each chosen global normalization. The member chosen at zero gives the test needed by the subsequent strip argument.

This is an internal derivation for the product of ordinary Rankin–Selberg integrals in J. W. Cogdell, *Analytic Theory of L-Functions for GL(n)*, chapter 9 of Bernstein and Gelbart, eds., *An Introduction to the Langlands Program*, Birkhäuser, 2004, Theorem 4.2, printed pp. 221–222. The local analytic premises use Jacquet, *Archimedean Rankin–Selberg Integrals*, 2009, Theorems 2.1 and 2.6, author PDF pp. 6–10.

`hasCoveringUnequalNormalizedGrowthTests_of_local_at` obtains real generation only at a real place. The complex generation and the placewise growth estimates enter as before.

The prescribed-tuple entry point
`exists_normalizedUnequalPureTest_of_prescribed` keeps the product identity
for any supplied normalized local tests and states its nonzero scalar.
The covering and growth construction applies it after choosing the local
tests at each point.
