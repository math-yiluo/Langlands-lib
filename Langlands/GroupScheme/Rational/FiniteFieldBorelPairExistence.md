# Existence of Borel pairs over finite fields

This internal derived module proves the existence clause of the
published `FiniteFieldBorelPairStatement`, using published Library theorems.

First, absolute Borel conjugacy and the existing Lang construction produce a
Frobenius invariant Borel over the algebraic closure. The existing effective
descent theorem supplies a geometric Borel over the original finite field.

Next, `finiteFieldGeometricMaximalTorus` supplies a torus in this descended
Borel which is maximal both over the original field and its algebraic closure.
The absolute Borel maximal torus theorem gives some ambient maximal torus
factoring through the geometric Borel. Conjugacy of maximal tori inside that
smooth connected solvable Borel proves that the chosen torus is also maximal in
the ambient group over the algebraic closure. Faithfully flat reflection then
gives ambient maximality over the original field. Its factorization through the
Borel gives the required containment of all-test subgroup functors.

All finite fields and all smooth connected affine ambient groups are covered;
there is no reductivity hypothesis. The module's provenance is this composition
of existing Library results for the existence clause of Milne's Proposition
17.99, as documented in the unchanged target statement.
