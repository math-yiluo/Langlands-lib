# Identity components of field group schemes

This module retains two independently constructed interfaces with their original hypotheses and namespaces.

## Affine finite-type groups

`FiniteTypeIdentityComponent.groupScheme H` is the actual open and closed identity
component of an affine group scheme of finite type over any field, with no
smoothness or reducedness hypothesis. `FiniteTypeIdentityComponent.inclusion H`
is its inclusion. Its topological range is the connected component of the
identity point. It is affine and locally of finite type, geometrically connected
and geometrically irreducible.

This internal construction generalizes the existing smooth identity-component
wrapper without changing that wrapper. Its input is the already published
ported theorem
`GoodReductionJacobian.RelativeGroupLaw.exists_isOpenImmersion_geometricallyConnected_range_eq_connectedComponent`,
whose hypotheses are local finite type and quasi-compactness. Applied to the
actual group law it gives the open and closed geometric identity component.
The module takes the corresponding open subscheme, lifts the unit,
multiplication and inversion through its inclusion, and uses the published
`GroupObjectDescent.grpObjOfMono` to obtain its actual group-scheme structure.
Multiplication lands in that component because its domain is connected; the
geometric connectedness supplied by the input theorem ensures this product
connectedness. All lifted operations agree with those of `H` after inclusion.

`FiniteTypeIdentityComponent.inclusion_comp_flat_surjective` proves that a flat
homomorphism from `H` to a connected affine group of finite type remains flat
and becomes surjective when restricted to this component. The restricted map
is flat because the component inclusion is open. Its range is open by finite
presentation, and is also closed by the published affine fppf image
factorization, which applies without smoothness. This nonempty open and closed
range is the whole connected target.

These statements are derived from existing Library results. No rigidity,
centrality or extension-splitting assertion is assumed or proved here.

## Locally finite-type groups

`finiteTypeIdentityComponent G` is the actual open subscheme of a group scheme
`G` locally of finite type over a field on the connected component of its
identity point. No smoothness, reducedness, perfectness or affineness assumption
is required for its construction. `finiteTypeIdentityComponentι G` is its actual
inclusion as a group-scheme homomorphism. The inclusion is open and closed, and
its range is `IdentityComponent.identitySet G`.

The component is connected and geometrically connected. It is locally of finite
type and, when `G` is affine over the field, affine over the field. Conjugation by
every point of `G` over every test scheme preserves its range subgroup functor.
Every homomorphism from a connected group scheme factors uniquely through this
inclusion. A connected open and closed subgroup is isomorphic to this component,
compatibly with the inclusion. Formation commutes with arbitrary extensions of
the ground field, by the actual base-change isomorphism and its inclusion law.

The construction uses the Library's openness theorem for connected components
of locally Noetherian schemes. The rational identity section factors through
this open component. The published pointed connectedness theorem makes it
geometrically connected. Thus its product with itself is connected, and the
multiplication and inverse of `G` restrict to it. Cancellation through the open
immersion proves the group laws through `GroupObjectDescent.grpObjOfMono`.
Normality follows because every fibre of the conjugation domain's projection to
`G` is connected and contains a point sent to the identity. The universal
factorization uses the range criterion for open immersions. After any field
extension the component stays connected and the pulled-back inclusion stays
open and closed; the characterization identifies it with the new component.

### Provenance

Milne, *Algebraic Groups* (2022 corrected reprint), Proposition 1.34, printed
p. 17 (PDF p. 28), states that the identity component is an algebraic subgroup,
formation commutes with field extension, and it is geometrically connected.
The registered original is `milne-2022-algebraic-groups`, SHA-256
`f2ddd8fa4d263085f173934664b246007a2c0bd539739b7c82de39bfb5d21f40`.
This passage and the full registered official errata snapshot
`milne-2022-algebraic-groups-errata-2026-11-04` were read; no correction to
Proposition 1.34 is listed.

The result is derived infrastructure. Its scope allows a group scheme merely
locally of finite type, and records each actual morphism and factorization
explicitly. The construction and normality/factorization proofs adapt the
published smooth-only `IdentityComponent` implementation, using
`PointedConnectedComponentGeometry` in place of smoothness to obtain geometric
connectedness. That published module and all its imported pairs remain
unchanged. No geometric irreducibility, component quotient, multiplicative-type
classification or linear reductivity theorem is asserted here.
