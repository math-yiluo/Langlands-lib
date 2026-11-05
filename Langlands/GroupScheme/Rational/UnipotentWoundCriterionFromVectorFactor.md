# The central additive-subgroup criterion from the vector-factor theorem

This internal derived construction concludes the exact published proposition
`UnipotentWoundCriterionStatement.{u}` under one explicit prerequisite:
`RelativeRoot.CommutativePTorsionVectorFactorStatement.{u}`. It removes the
algebraic separably closed rational-point premise from the earlier reduction.
The original statement pair, its imports and the representation-based
`IsUnipotent` predicate are unchanged. Every field and characteristic remain in
the conclusion. The full unconditional target remains open until the
vector-factor proposition is proved.

In prime characteristic,
`exists_central_additive_closed_subgroup_of_charP_of_vectorFactor` uses the
published pointed power-family extraction to obtain a nontrivial family in a
smooth connected affine central closed subgroup killed by `p`. The supplied
factor proposition decomposes that actual subgroup as an actual vector group
times a smooth connected affine complement that becomes affine-line rigid over
the separable closure. The whole basepoint section remains the identity.

The new unconditional smooth-family density and field-descent theorem proves
that the complement projection is trivial. Nontriviality therefore forces
positive vector dimension. The existing coordinate-block construction provides
an actual closed additive line in the vector factor. Its inclusion through the
product and the original subgroup is closed, and centrality follows from the
centrality of that subgroup. All vector coordinates retain naturality on every
relative scheme test. `criterion_of_charP_of_vectorFactor` combines this
existence result with the already established unrestricted forward implication.

`criterion_of_vectorFactor` splits the ground field into characteristic zero
and prime characteristic. The former uses the unconditional characteristic-zero
criterion; the latter uses the preceding one-premise criterion. The conclusion
is the unchanged exact named all-field proposition, not a replacement statement.
`centralAdditiveLineOfVectorFactor` then chooses the resulting actual central
closed additive subgroup when affine-line constancy fails.

The implementation reuses the earlier line-through-factor closedness and
centrality lemmas and the characteristic-zero branch unchanged. The new
smooth-density theorem discharges the earlier rational-point premise by local
étale polynomial charts and actual separably closed point lifting. This unit
neither proves nor assumes a coordinate presentation in place of the remaining
vector-factor theorem; that exact theorem is retained as its explicit argument.
