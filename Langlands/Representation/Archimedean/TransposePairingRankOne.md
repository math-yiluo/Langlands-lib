# Rank-one inverse-transpose pairing construction

This internal helper constructs the bilinear square of a nonzero linear functional and proves the transpose-pairing condition in matrix size one. It uses irreducibility, admissibility, compact finiteness, continuity of compact matrix coefficients, and the actual compact adjoint covariance. It imposes no unitary or genericity condition on the module.

All matrices of size one commute and equal their ordinary transpose. Their complexified real Lie algebra is abelian; the proof retains the full tensor product over the reals for either real or complex coefficients. Covariance therefore makes the compact and Lie actions commute. Schur's lemma from GKModuleDensity makes each action scalar. Inverse transpose on the compact group is inversion, and its differential on the full complexification is negation. Thus the bilinear square of any functional is invariant. A functional taking value one on a nonzero vector gives a nonzero square.

This proves only the matrix-size-one case, not the arbitrary-rank transpose-pairing statement. No globalization or contragredient identification is asserted. The construction and proof are internal consequences of the existing module predicates and Schur lemma.

`realTransposePairing_rankOne` and `complexTransposePairing_rankOne` take exactly the corresponding Library module, irreducibility and admissibility predicates for size one. The arbitrary carrier universe remains free. Compact orbit spans supply the finite stable subspaces required by Schur's lemma. The differentiation clause of the module predicate is not needed for this scalar argument.
