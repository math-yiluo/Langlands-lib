# Base change of actual automorphic actions and cocycles

This internal construction works over any base schemes `S` and `S'` in the
same universe and any morphism `b : S' ⟶ S`. The acting group `H`, the target
group `V`, and their action are actual group schemes and an
`AutomorphicAction H V`.

`AutomorphicAction.baseChange` constructs an actual automorphic action of the
pulled-back `H` on the pulled-back `V`. On each test scheme over `S'`,
`baseChangeAct` transports the original action through
`baseChangePointsEquiv`, the group isomorphism supplied by the scheme pullback
adjunction. Naturality and the action identities transfer through these
isomorphisms. The existing `ofPoints` construction then supplies the actual
action morphism. `baseChange_act` and `baseChangePointsEquiv_act` record its
pointwise formula and its intertwining with the original action.

`Cocycle.precomp` restricts any relative cocycle along an actual homomorphism
`K ⟶ H`, using the restricted action on `V`. Its morphism is the original
cocycle morphism precomposed on the acting-group factor. `eval_precomp`
identifies its evaluation.

`Cocycle.baseChange` pulls back a cocycle whose parameter scheme is the base
`Over.mk (𝟙 S)` to a cocycle parametrized by `Over.mk (𝟙 S')`. Its evaluation
transports the original cocycle evaluation through the same actual point
isomorphisms. Naturality constructs the cocycle morphism on the product of the
new base and the pulled-back acting group; the original normalized cocycle
identities imply its normalized identities on every test scheme.
`eval_baseChange` proves the stated evaluation formula.

`Cocycle.baseChange_coboundary` proves equality of the pulled-back coboundary
with the coboundary of `baseChangeBasePoint b V v`, for each actual base point
`v`. The proof uses evaluation extensionality, the action intertwining formula,
and the existing compatibility of constant point families with pullback. The
unique map of a test scheme to the base identifies the constant family in
these formulas.

These are derived constructions from the published actual-action, cocycle,
and pullback-point interfaces; no external geometric theorem is used. The
module asserts neither vanishing of cocycles nor existence of rational
conjugators. It supplies transport needed for later splitting-field arguments.
