# The twisted Mumford homomorphism in the integral Harris order

Fix the Harris arithmetic data and signature charts, an actual abelian
scheme, a dual witness and the prerequisites for the dual maps. Let
`i` be an actual ring action of the Harris integral order and `lam`
an actual homomorphism to the dual satisfying `IntegralRosatiEquations`.
Write `tau` for `CentralSimpleUnitaryData.harrisHodgePELIntegralInvolution`,
the positive auxiliary left involution restricted to the order.

`harrisMumfordTwistOrderElement` defines the common element `j + tau(a) * a`
of the fixed integral order for an order element `a` and natural parameter `j`.
It specifies the same source endomorphism for every family with the given
Harris order.

`IntegralRosatiEquations.nsmul` follows from additivity of composition in
each hom group. For an order element `a` and a natural number `j`,
`IntegralRosatiEquations.mumfordTwist_eq` writes the sum of `j • lam` and
the pullback of `lam` by the actual endomorphism `i a` as the endomorphism
`i (j + tau a * a)` followed by `lam`. Apply the Rosati equation to
`tau a`, use `AlgebraInvolution.apply_apply`, and use the ring action
with the usual diagrammatic composition convention for endomorphisms.

For `lam` the Mumford map of an ample bundle, the displayed sum is the
map in `Rosati.MumfordEulerDegreeStatement` controlling the Euler
characteristic of the pulled-back bundle twisted by its `j`th power.
The integral identity permits comparison of these ranks through the
action of one fixed order element.
