# Action laws on a universal fibre product

Author: Worker 706.

This internal helper rewrites the action interface as finitely many morphisms
and equalities. It follows directly from the fibre product universal property
and the already constructed relation operations; no approximation or descent
result is assumed. The motivation is descent of the chart and its action in
Stacks Project Proposition 70.8.1, Tag 07SU, registered as
`stacks-noetherian-approximation-2026-11-01`.

In the namespace `EtaleEquivalenceRelation.Action`, `composable E p` is the
scheme of two composable arrows `r,q` of `E`, together with a point of `P`
over the source of `q`. It is the fibre product
`E.R ×_{E.U,s,t∘fst} (E.R ×_{E.U,s,p} P)`.
The morphisms `outerArrow`, `innerArrow`, and `sourcePoint` are its three
projections. The equations `outer_inner` and `inner_source` record their
compatibility. `composableLift` constructs the corresponding morphism for
any test scheme; its three projection lemmas recover the supplied data.

For a prospective action morphism `a` satisfying the target equation `ha`,
`successive a ha` acts first by the inner arrow and then by the outer arrow.
`composite a` acts by their composite. The proposition `Associative a ha`
equates these two morphisms. `associative_universal` proves this equality
for every existing action by specializing its associative law to the three
universal projections.

Conversely, `ofAssociative` constructs an action from its morphism, target
equation, unit equation, and this one universal associative equation.
For arbitrary test-scheme data it precomposes that equation with
`composableLift`. Fibre product uniqueness identifies the left side with
successive actions. On the right, endpoint uniqueness in `E` identifies the
composite arrow, and fibre product uniqueness identifies the action input.
All schemes and test schemes retain arbitrary universe `u`. The constructor
is a criterion for action laws; it does not itself assert that data descends.
