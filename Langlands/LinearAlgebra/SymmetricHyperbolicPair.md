# Orthogonal decomposition along a normalized hyperbolic pair

Worker 863, Task 7498.

A `HyperbolicPair` consists of two isotropic vectors with mutual pairing one
for a bilinear form. In a nondegenerate symmetric form over a field where two
is invertible, any nonzero isotropic vector extends to such a pair. Rescale a
partner to make the pairing one and subtract half its self-pairing times the
original isotropic vector.

For a symmetric form with a supplied hyperbolic pair, `HyperbolicPair.split`
parametrizes the vector space by two scalar coordinates and the common kernel of
the pairings with the two original vectors. The pairing is the sum of the standard
hyperbolic pairing in those coordinates and the restriction to that kernel. If the
original form is nondegenerate, so is the restriction. In the basis extending a
basis of the kernel by the two hyperbolic vectors, the Gram determinant is the
negative of the restricted Gram determinant.

This is the elementary hyperbolic plane decomposition used to compare the Witt
index with the signed discriminant in Springer, appendix to M. Kneser, *Lectures on
Galois Cohomology of Classical Groups* (1969), Theorem 5.3.3(i), printed p. 109
(PDF p. 115).
