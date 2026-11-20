# Picard triviality for finite étale covers of affine space

`Langlands.Algebra.affineSpaceFiniteEtalePicardTrivial` proves
`Langlands.Algebra.AffineSpaceFiniteEtalePicardTrivialStatement.{u}` for every
universe `u`. The statement is the affine-space input used in Conrad,
*Reductive group schemes* (2014), Remark 7.2.13, p. 259.
[Statement and source](AffineSpaceFiniteEtalePicardStatement.md)

The proof applies `affineSpaceFiniteEtalePicardTrivial_of_polynomialProduct`
to `affineSpaceFiniteEtalePolynomialProduct`. The latter gives a ring
isomorphism from the covering algebra to a finite product of polynomial
rings over fields. Its proof uses geometric splitting over the algebraic
closure and Galois descent.
[Polynomial product proof](AffineSpaceFiniteEtalePolynomialProductProof.md)

Each polynomial ring over a field is a unique factorization domain and
has trivial Picard group. The reduction obtains Picard triviality for the
finite product and transports it along the ring isomorphism to the
covering algebra. This proves `Subsingleton (CommRing.Pic A)` for the
finite étale algebra in the target, including dimension zero and the
zero algebra.
[Picard reduction](AffineSpaceFiniteEtalePicardReduction.md)
