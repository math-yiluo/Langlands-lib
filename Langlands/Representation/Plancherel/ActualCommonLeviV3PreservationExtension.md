# Extending exact common-Levi preservation to the unitary parameters

This internal reduction applies to a comparison family with the ambient
regular representatives required by `IsRegularUnitaryExtension`. In each
representative's open neighborhood the denominator is nonzero. Testing the
numerator by a linear map into a normed complex space preserves its finite
polynomial expansion. Restricted to the unitary group, the quotient is
continuous after each such test and on every fixed input vector.

The fixed test for the coefficient at the identity is
`compactCoefficientAtOne`. Its values agree on the two sides if the exact
coefficient at the identity is preserved on a dense unitary subset of the
genuine generic locus. Continuity gives that equality on the full unitary
group. The full product action by `(g, 1)` then identifies the coefficient at
`g` with the coefficient of the translated vector at the identity.
Equivariance gives the equality for every coefficient argument.

`formalDegreeCompactValue` sends the fixed source compact tensor into the
normed carrier of the target's fixed formal-degree form. Pairing two such
values is continuous in the unitary parameter. The source form is constant
on a fixed pair of vectors in its compact model, so equality on the dense
unitary set extends to all parameters. Transport back gives the exact
`formalDegreeForm` used by the closed target.

The reduction serves the coefficient and form identities in Waldspurger
(2003), Lemma V.3.1, printed p. 295, PDF p. 61. Its hypotheses supply the
regular family and generic identities, while its conclusions give the
identities at every unitary parameter.
