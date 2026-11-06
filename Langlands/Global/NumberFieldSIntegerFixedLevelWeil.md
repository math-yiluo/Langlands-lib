# Enlarged levels of the fixed number-field Weil model

This derived construction implements the enlarged-support step in Conrad,
*Weil and Grothendieck approaches to adelic points* (December 31, 2011),
Example 4.2, printed pp.9–10. Fix actual number fields K and L with their
original embedding, a finite set S of finite lower places, and any finite
support T containing S. The original lower ring A is the ring of
S-integers of K; the original upper ring B is the ring of integers of L
away from the full preimage of S. Both rings remain fixed as T enlarges.
Every infinite place occurs in the full adelic level.

The original `NumberFieldSIntegerLevelWeil.Above` and `upperFactor` at
support T give all upper places above each original lower coordinate and
their actual completed fields or completed integer rings. Their finite
index families, local ring topologies, open units, finite projective
module structures and module topology comparisons are reused from that
module. The lower A-action is the original action restricted along the
literal inclusion from S-integers to T-integers, as defined by
`FixedModelLocalProduct.numberFieldFactorAlgebra`.

`upperCoefficientAlgebra` keeps the original B-action at every factor:
the native inclusion in an upper completed field, and the original
completed-integer map outside T. In the last case, T containing S proves
that the lower place lies outside S, so the existing integral tensor
comparison over A and B applies. No new coefficient ring or arithmetic
localization theorem is assumed.

`tensorEquiv` constructs the completed tensor comparison over these fixed
rings at every enlarged-level coordinate. Infinite and finite field
coordinates reuse the existing arbitrary-place S-integer tensors.
Integer coordinates reuse the existing outside-S tensor. The private
`tensorData` transports both the equivalence and its coefficient law
along equality of the native and restricted A-actions, proved by
`Algebra.algebra_ext` and literal equality of coefficient maps.
`tensorEquiv_one_tmul` identifies the image of every right coefficient
with its original B-action. There is no additional separability premise.

`levelFactorAlgHom` is the literal projection from
`numberFieldAdeleLevelOver K S T`, regarded as an A-algebra map. Its
`toRingHom` is exactly `numberFieldLevelFactorProjection K T.val i`, as
proved by `levelFactorAlgHom_toRingHom`.

Let Y be an actual scheme over B, locally of finite type, quasi-compact
(`CompactSpace Y.left`) and quasi-separated, with a specified relative
immersion into a finite-dimensional projective space over B. The
immersion derives separatedness and finite affine neighborhoods. Let W
be the existing actual `affineChartWeilRestriction A B Y`.
`levelPointHomeomorph` identifies W-points over the actual enlarged lower
level with the product of all the original upper local Y-point spaces,
indexed by a lower coordinate and an upper place above it. Its source
has the independently defined `numberFieldFixedModelStageTopology K S W T`;
each target factor has its existing `schemePointTopology`, and the target
has the product topology.

The proof composes `FixedModelLocalProduct.numberFieldStageHomeomorph`,
which compares this existing stage topology with the local product
point topology over fixed A, with `productTensorWeilPointHomeomorph`
using the actual tensors above. It assumes no finiteness or separation
property of W. The product-point equivalence is supplied by the original
upper model and the proved Weil comparisons.

`levelPointHomeomorph_component` identifies every output coordinate with
`completedTensorWeilRestrictionPointMap` after change of the input point
along `levelFactorAlgHom`. The proof uses composition of the actual test
spectrum maps and the original product Weil coordinate law. Thus the
homeomorphism retains the original local counits and literal projections.

This unit supplies the fixed-base enlarged number-field comparison.
Regrouping its target into the actual upper enlarged level, compatibility
with support inclusions, and passage to full adelic points remain separate
host obligations; it does not claim the full Example 4.2 conclusion.
