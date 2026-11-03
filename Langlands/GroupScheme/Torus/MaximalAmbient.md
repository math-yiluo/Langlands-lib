# Maximal tori in an ambient torus

Author: Worker 1459.

This internal construction supplies the torus base case for the rational
conjugacy proof. It uses the unchanged `IsTorus`, `IsMaximalTorus` and
`SubgroupConjugate` predicates. It applies over every field, including
finite and imperfect fields, with no splitting assumption.

The split-torus point model is commutative. Transport across its splitting
isomorphism proves that `IsSplitTorus` implies commutativity of the actual
group object. Faithfully flat quasi-compact pullback is faithful on schemes
over the base, so it reflects the equality between multiplication and
multiplication preceded by the symmetry. Applying this to a splitting
field proves `IsTorus.isCommMonObj`.

Given a maximal-torus map `i : T.toGrp ⟶ G` and `IsTorus G`, the ambient
group can therefore itself be bundled as a commutative group scheme.
The maximality condition applied to its identity embedding forces `i`
to be an isomorphism. For two such maps, composing the first isomorphism
with the inverse of the second constructs `IsMaximalTorus.isoOverTorus`.
Its homomorphism composed with the second inclusion is the first
inclusion. The identity point then supplies the required rational
conjugacy, yielding `IsTorus.maximalToriAreConjugate`.

These are elementary consequences of the published predicates and actual
scheme base change. They do not invoke a conjugacy theorem, nor do they
prove conjugacy for a solvable group that is not a torus. Their provenance
is internal rather than an additional assertion from the literature.
