# Reduction of the root comparison field to doubled-root depth models

This derived unit composes the concrete apartment-lift root helpers, uniform
root-fibre depth comparisons, conditional doubled-root block descent, and
integral-vector centralizer containment. It makes no new assertion attributed
directly to original literature.

For a supplied apartment lift `L`, `HasRootFiberBlockDescent` means that every
lower rational point whose extension lies in the upper positive root-fibre
span at a nonnegative uniform depth belongs to the lower ordered block
`U_(a,y,r) U_(2a,y,r)`. It quantifies over every lower apartment point, actual
lower root, and nonnegative depth. It does not require a separate premise that
the point already belongs to the lower root group.

`hasRootFiberBlockDescent_of_doubledRootDepthModel` derives this property from
the exact proposition `UnramifiedDoubledRootDepthModelStatement`, retaining the
supplied building data's apartment axioms. If `2a` is absent from the lower
relative roots, the existing uniform-fibre preimage theorem puts the point in
the lower `a` filtration and the identity supplies the second factor. If `2a`
is a root, the intrinsic doubled-root subgroup has a smooth closed
representative. Applying the model-existence premise to that representative
at depth `2r` gives a smooth model with connected special fibre and the exact
comparison on all maximal-unramified points. This is precisely
`IsDoubledRootDepthModelAt y a r q M`. The conditional doubled-root descent
theorem then gives the block with both factors at their original depth `r`.
Neither branch needs an initial root-group membership premise.

`exists_rootComparison_of_rootFiberBlockDescent` assembles all seven fields
for the positive integral restriction fibre. A nonzero lower root admits an
integral cocharacter with positive pairing. Tensoring this cocharacter with
`1 : ℝ` and transporting it through the actual base change and comparison
torus gives the required upstairs vector. The root helpers give closure,
positivity, positive and negative root-group containment, and forward
filtration containment. The centralizer-containment theorem applies to every
integral downstairs cocharacter, so it gives the Levi field for this same
positive vector. The supplied block property gives the final field; its
stronger conclusion allows the structure's root-group premise to be unused.

Consequently `unramifiedComparisonRootField_of_doubledRootDepthModel` proves
the implication from `UnramifiedDoubledRootDepthModelStatement.{u}` to the
unchanged `UnramifiedComparisonRootFieldStatement.{u}` at arbitrary universe
`u`. It applies to every supplied lift, without constructing such a lift.
The depth-model proposition remains an explicit, unproved premise. This unit
does not prove the unconditional root-field target or permit adding a premise
to that target; an actual proof of model existence is still required.
