# Enlarged levels of the fixed curve Weil model

This derived construction implements the enlarged-support step in Conrad,
*Weil and Grothendieck approaches to adelic points* (December 31, 2011),
Example 4.2, printed pp.9–10. Fix a finite field k, a function field K
over k with its specified rational-function action and compatible scalar
tower, and a finite extension L of K over k. No separability is assumed.
Choose s in K with K finite-dimensional over k(s), and a nonzero
element t of the original curve chart ring. Let S be the existing
`curvePlacePrincipalExceptional k K s (t : K)`. The lower ring A is the
original `curvePlaceSIntegers k K S`, and the upper ring B is the original
S-integer ring of L at the full preimage of S. For every finite support T
containing S, both A and B remain fixed.

`lowerPlace` and `Above` index each lower T-level coordinate and every
original upper place above it. `upperFactor` is the original upper
completed field when the lower place belongs to T, and the original
completed valuation ring when it lies outside T. The scoped instances
reuse the actual commutative local topological rings, open units, and the
proved finite projective module and module-topology comparisons for
these completions. The lower A-action on each factor is the original
action restricted along the literal inclusion from S-integers to
T-integers, supplied by `FixedModelLocalProduct.curveFactorAlgebra`.

`upperCoefficientAlgebra` retains the original B-action: the native map
into an upper completed field, and the existing map into the original
completed integer ring outside T. If a lower place lies outside T, the
inclusion of S in T proves that it lies outside S. This supplies the
existing integral tensor comparison over the original A and B.

`tensorEquiv` constructs the completed tensor comparison over A and B
at every enlarged-level coordinate. At field coordinates it reuses
`CurvePlacePrincipalSIntegerFieldTensor.tensorEquiv`, which applies at
every lower place. At integer coordinates it reuses
`CurvePlacePrincipalSIntegerLocalTensor.completedTensorEquiv`.
The private `tensorData` transports these equivalences and their
coefficient laws along equality of the native and restricted A-actions.
That equality follows from `Algebra.algebra_ext` and the literal
coefficient maps. `tensorEquiv_one_tmul` identifies every right
coefficient with its original B-action. No change of the integral bases
or new localization theorem is assumed.

`levelFactorAlgHom` is the literal projection from the original enlarged
level `curvePlaceAdeleLevelOver k K S T`, regarded as an A-algebra map.
`levelFactorAlgHom_toRingHom` proves that its underlying ring map is
exactly `curvePlaceLevelFactorProjection k K T.val i`.

Let Y be an actual B-scheme, locally of finite type, quasi-compact
(`CompactSpace Y.left`) and quasi-separated, with a specified relative
immersion into a finite-dimensional projective space over B. The
immersion derives separatedness and finite affine neighborhoods. Write
W for the existing actual `affineChartWeilRestriction A B Y`.
`levelPointHomeomorph` identifies actual W-points over each enlarged
lower level with the product of all original upper local Y-point
spaces, indexed by a lower coordinate and an upper place above it.
The source has the independently defined
`curvePlaceFixedModelStageTopology k K S W T`; every target factor has
its original `schemePointTopology`, and the target has the product
topology.

The proof composes `FixedModelLocalProduct.curveStageHomeomorph`,
which compares the existing stage topology with the local product point
topology over fixed A, with `productTensorWeilPointHomeomorph` using
the actual tensors above. It assumes no additional finiteness or
separation property of W. The product-point equivalence uses the
original upper model and the proved Weil comparisons.

`levelPointHomeomorph_component` identifies each output coordinate
with `completedTensorWeilRestrictionPointMap` after coefficient change
along `levelFactorAlgHom`. The proof composes the actual test-spectrum
maps and applies the original product Weil coordinate law. Thus the
homeomorphism preserves the original local counits and projections.

This unit supplies the enlarged fixed-base comparison for function
fields. Regrouping its target into the actual upper enlarged level,
compatibility with support inclusions, and passage to full adelic points
remain further host obligations. It does not claim the full Example 4.2
conclusion.
