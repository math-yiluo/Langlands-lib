# A connected commutative envelope for a positive power

For an affine group scheme locally of finite type over any field `k : Type u`
and an actual rational point `x`, `ConnectedCommutativePowerEnvelope G x`
records a smooth affine commutative group scheme `C`, its closed inclusion into
`G`, an actual rational point `y` of `C`, and a positive natural number `m` with
`rationalPoints.map inclusion y = x ^ m`. It also records connectedness and
geometric connectedness of `C`. There is no perfection or characteristic
assumption and no ambient smoothness assumption.

The derived constructor `connectedCommutativePowerEnvelope` first applies
`smoothCommutativePointEnvelope` to the cyclic closure of `x`. It then takes
that smooth affine group's actual identity component. The commutative group
structure on the identity component is obtained by testing arbitrary scheme
points and canceling its monic inclusion; it is therefore commutative on all
tests. The component and its inclusion inherit smoothness, affineness,
geometric connectedness and closedness from the published identity-component
construction.

`IdentityComponent.positivePowerExponent` is the order of the permutation of
the finite set of connected components induced by translation by the lifted
point. Its positivity is supplied by `positivePowerExponent_pos`.
`positivePowerPoint` lifts this power through the identity-component inclusion.
The constructor composes that inclusion with the original cyclic-closure
inclusion. Its point equation follows from `positivePowerPoint_inclusion`, the
original closure point equation, and preservation of powers by
`rationalPoints.map`. No new structural existence theorem or source assertion
is assumed here: this is an adapter of those two existing constructions.
