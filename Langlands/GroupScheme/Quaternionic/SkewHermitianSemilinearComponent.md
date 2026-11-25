# Semilinear multiplication on the symmetric component

For quaternion coordinates with embedded quadratic field `E`, left multiplication
by the second generator `j` gives the bijective conjugate-semilinear map `jAction`.
Its square is the scalar `δ = j²`, where the scalar is read in `E`.

For the symmetric component `H` of the skew pairing `B` and `T = jAction`,
`H(Tx,y)` is the conjugate of the first quaternion coordinate of `B(x,y)`,
and `H(x,Ty)` is its negative without conjugation. The identity
`H(Tx,Ty) = -δ conjugate(H(x,y))` follows from the quaternion table. The two
scalar equations `H(x,x) = H(Tx,x) = 0` are equivalent to `B(x,x) = 0`.

If `u,v` lie in a totally isotropic subspace of `H` and two is nonzero in `E`,
then the skew self-pairing of `u + Tv` vanishes precisely when `H(u,Tv) = 0`
and `H(u,Tu) + δ H(v,Tv) = 0`. Expand the two component equations and use
symmetry, the semisimilarity identity, and `T² = δ`.

These are the coordinate identities in Springer, appendix to M. Kneser,
*Lectures on Galois Cohomology of Classical Groups* (1969), Theorem 5.3.3(i),
equations (4)–(5), printed p. 110 (PDF p. 116).
