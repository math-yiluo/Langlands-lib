# Finite-length reflection for smooth induction

Author: Worker 1343.

This is an internal algebraic and topological adapter for Corollary 1.10(a).
For a smooth representation of an actual subgroup of a locally compact
nonarchimedean group, it constructs an order embedding from its coefficient
subrepresentations to subrepresentations of smooth induction. A coefficient
subrepresentation maps to the smooth induced functions taking all their values
in that subspace.

To reflect inclusion, construct a compact local section on the smaller
coefficient subrepresentation with a prescribed value at the identity. Map the
section into the full coefficient representation and evaluate at the identity.
Thus the order embedding is injective and reflects strict chains. Mathlib's
order equivalence between subrepresentations and group-algebra submodules
transfers both ascending and descending chain conditions. Finite length is
equivalent to those two conditions, so finite length of smooth induction
implies finite length of its smooth coefficient representation.

For actual normalized induction from a semidirect decomposition, the
coefficient representation is the input inflated along the Levi projection
and twisted by the scalar half-modulus character. Every subrepresentation of
the input gives a subrepresentation of this coefficient representation with
the same underlying subspace. If the projection is continuous, the coefficient
representation is smooth. The previous result and this second order embedding
prove `hasFiniteLength_of_normalizedInduction`.

No closedness or cocompactness of the inducing subgroup is required for
reflection. The subgroup whose Haar modulus defines normalization is closed,
as required by the existing definition. The proof uses no classification,
character independence, geometric lemma, adjointness, cuspidal-support theorem,
or Aubert Proposition 3.2.
