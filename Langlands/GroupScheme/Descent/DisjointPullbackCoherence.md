# Direct pullback assembly on arbitrary disjoint components

This internal construction extends actual pullback assembly to an index type
in the same universe as the schemes, with no finiteness hypothesis. It uses
`DisjointComponents.groupIso` and its restriction and extensionality laws.

`pullbackIsoAlong` first changes each specified direct-pullback endpoint to the
iterated pullback over its component, and then assembles the resulting actual
group-scheme isomorphisms. Its restriction to each component is the given
isomorphism. Restrictions detect equality of both morphisms and isomorphisms,
since conjugation by the direct/iterated comparisons is invertible and the
underlying component restriction functor is faithful.

`pullIso_pullbackIsoAlong_factor` evaluates an assembled isomorphism along any
map factoring through a specified component. The proof uses the published
successive-pullback coherence and the component restriction identity.
Transport along the identity map fixes actual morphisms and isomorphisms;
the morphism proof compares their two actual scheme pullback projections.
Transport also preserves composition of isomorphisms by `pullHom_comp`.

`CoproductComponents` records the actual inverse images of all components of a
scheme coproduct under a map from an arbitrary test scheme. The inclusions
give a disjoint decomposition of that test scheme by
`DisjointComponents.projection_isIso`. A coordinate factorization gives a map
into the appropriate inverse image, with the stated two projection identities
by the universal property of the pullback.

All content is derived internally from actual scheme pullbacks and coproducts
and the previously constructed fully faithful component restriction functor.
The module supplies assembly and coherence, with no assertion of effectivity
of arbitrary descent data.
