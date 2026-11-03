# Functoriality and reductivity transport for identity components

This is an internal, derived API for the published construction
`Langlands.GroupScheme.identityComponent`. It uses the universal factorization
through the open identity-component inclusion and the published uniqueness of
representatives of an all-test subgroup functor. No external mathematical source
is required for these categorical consequences.

For a field `k` in any universe, `IdentityComponent.map` restricts a homomorphism
between smooth affine group schemes over `k` to their actual identity components.
The defining factorization gives `map_identityComponentι`. Cancelling the open
immersion of the target identity component proves preservation of identities and
composition. Applying the restriction to an isomorphism and its inverse gives
`IdentityComponent.mapIso`, with its two inclusion compatibility formulas.

If the original smooth affine group scheme is connected,
`IdentityComponent.connectedIso` identifies its identity component with the
original group scheme. Its inverse is the factorization of the identity
homomorphism through the identity component, and its forward map is the actual
identity-component inclusion. The factorization formula and cancellation of
that inclusion prove the two inverse laws.

`IdentityComponent.isConnectedReductive_of_iso` transports connected reductivity
of identity components along `mapIso`, using the published
`IsConnectedReductive.of_iso` theorem. The same transport along `connectedIso`
proves `IsConnectedReductive.identityComponent`.

For two smooth affine group schemes representing the same subgroup functor,
`SubgroupFunctor.IsRepresentedBy.identityComponentIso` restricts the canonical
isomorphism of representatives to their identity components.
`identityComponentIso_hom_comp` says that the two resulting maps to the ambient
group agree. `isConnectedReductive_identityComponent` consequently transports
connected reductivity of the identity component from either representative to
the other.

These results preserve the actual open-subscheme identity-component construction
and require equality of the represented subgroup functors on every test scheme.
They do not establish reductivity of a centralizer without a reductivity result
for one representative.
