# Faithful flatness and the tensor comparison of a strongly graded ring

Internal derived algebra for affine quotients by central multiplicative-type
subgroups, continuing `StronglyGraded`.
For a coaction grading of a commutative ring A by any abelian group M, the
zero-coefficient map takes values in the degree-zero subring and splits its
inclusion. If each degree has a finite dual family, projectivity gives flatness;
applying the splitting to an ideal that spans A shows that the ideal is the
whole degree-zero ring. Thus A is faithfully flat over degree zero.

The canonical map A tensor_{A_0} A to A[M] sends a tensor b to a c(b).
Choose a finite degree m / degree -m partition of unity for every m. The inverse
sends the monomial of degree m with coefficient a to a times the tensor sum of
the chosen dual pairs, with the negative-degree member in the first factor.
Balancing over degree zero proves that a homogeneous b of degree m times that
tensor sum is 1 tensor b. Homogeneous decomposition proves the inverse identities.
No torsion-freeness or finite-generation hypothesis on M is used.

Provenance: internal strong-grading implementation of the affine torsor algebra
in SGA 3, Exposé VIII, Gille–Polo recomposition of 8 November 2009, §§4–5,
especially Theorem 5.1. Registered source `sga3-expose-viii-gille-polo-2009`,
SHA-256 `06e43e0571d411cc5579975778fcc03c8ecaa67189248d1a053e61dc653af510`.
This module asserts no scheme quotient and supplies no construction of the grading
or of the dual families from an action.
