# Identity-limit extensions lie in the actual identity component

This internal construction works over an arbitrary field `k : Type u` with
arbitrary universe `u`. Its group scheme `G` is smooth and affine. It uses
the published actual identity component, with its open and closed inclusion
`identityComponentι G`. No connectedness of `G` or of a test scheme is assumed.

`range_subset_identitySet_of_evalZero_eq_one` considers any actual morphism
`e : T × A¹ → G` whose value on the zero section is the identity. Each fiber
of `T × A¹ → T` is connected, because the affine line is geometrically
irreducible and hence geometrically connected. The image under `e` of
each such fiber is connected and contains the identity point, supplied
by the zero section. Thus the image of the whole family lies in the
connected component of the identity. The argument applies to every test
scheme, including disconnected and nonreduced ones.

`IdentityComponent.affineLineLift` lifts this family through the actual
open identity-component inclusion. Its composite is the original family.
Cancellation of that monomorphic inclusion shows that the lifted family's
zero value is still the identity.

`AutomorphicAction.unipotent_le_identityComponent` applies this lift to an
orbit extension with identity zero value for any automorphic `Gm` action.
Evaluating at the unit parameter recovers the original point, because the
unit acts as the identity. This proves containment of the actual all-test
identity-limit subgroup functor in the range of the identity component.
It does not assume representability or connectedness of that functor.

The provenance is internal: Mathlib's geometric irreducibility of affine
space and connectedness of geometric fibers, the published geometric
irreducibility-to-connectedness result, the actual identity component
and open-immersion lifting API, and the dynamic action definitions. The
fiberwise range proof adapts the method of
`IdentityComponent.range_conjOver_subset`, authored by Workers 947 and 967.
This file supplies a component-containment fact and no reductivity or
normalizer-existence theorem.
