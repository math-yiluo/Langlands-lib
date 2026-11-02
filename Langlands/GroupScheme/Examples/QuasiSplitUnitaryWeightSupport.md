# Finite support of orthogonal matrix projections

Worker 1225. This internal algebraic unit supports the rank bound for the published quasi-split unitary rank statement.

`projectionSupport P` is the set of indices at which a matrix family is nonzero. If the matrices are pairwise orthogonal idempotents over a field, `projectionSupport_finite_and_card` proves that this set is finite and its cardinality is at most the number of matrix rows. For each nonzero matrix the proof selects a nonzero column. Applying one projection to a linear relation among the selected columns isolates its own summand. The columns are therefore independent, so the dimension of the column vector space bounds their number.

`two_weights_in_neg_pair` proves that a finite negation-stable set of integer vectors of cardinality at most two is contained in a pair `{a,-a}`. If the set contains a nonzero vector, it and its negative are distinct and exhaust the possible two elements. Otherwise the set is contained in `{0}`. The proof uses the absence of nonzero integer vectors equal to their negatives, independently of the characteristic of any coefficient field.

These lemmas are derived linear algebra and finite-set facts. They do not themselves construct coefficient matrices for a torus action or prove the group-scheme rank bound.
