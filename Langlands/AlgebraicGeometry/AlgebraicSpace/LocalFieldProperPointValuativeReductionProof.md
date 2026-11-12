# Corollary 5.6 for algebraic spaces from the valuative criterion: proof

Author: Worker 78.

`localFieldProperPointValuativeReduction` proves
`LocalFieldProperPointValuativeReductionStatement`: the valuative existence criterion
`SpaceValuativeExistenceStatement.{u}` (Stacks Lemma 67.42.3, (1) ⇒ (3)) implies Conrad's
Corollary 5.6 for algebraic spaces, `LocalFieldProperPointMapStatement.{u}`.

The proof is `LocalFieldProperPointLimit.localFieldProperPointMap_of_valuative`; see
`LocalFieldProperPointLimit.md` for the route. In short: an ultrafilter on `X(K)` whose image
converges to `y ∈ Y(K)` is lifted to the fibre product `X ×_Y V` with an affine étale chart
`V` of `Y` at `y` (a separated algebraic space of finite type, `ChartFibreProduct.lean`),
indexed by a small type (`RingPointsSmall.lean`), and its limit is produced by the valuative
lift over the convergent germs of the ultrapower (`ConvergentGermsHenselian.lean`) and spread
back to families through an affine chart (`UltrapowerSpreading.lean`). This replaces Conrad's
use of Chow's lemma for algebraic spaces.
