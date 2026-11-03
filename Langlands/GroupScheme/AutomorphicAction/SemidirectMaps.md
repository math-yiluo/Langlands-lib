# Canonical morphisms and geometry of the semidirect group scheme

Let `B : Scheme.{u}`, let `H` and `G` be actual group schemes over `B`, and let
`a : AutomorphicAction H G`. This internal construction supplies actual
group-scheme inclusions `semidirectInl : G ⟶ a.semidirectProduct` and
`semidirectInr : H ⟶ a.semidirectProduct`, and the group-scheme projection
`semidirectProjection : a.semidirectProduct ⟶ H`. The base scheme and universe
are arbitrary throughout.

The construction first uses the ordinary semidirect product inclusions and
right projection to define natural group homomorphisms on the full point
presheaves. Pullback naturality of the inclusions uses preservation of the
identity point. The fully faithful group-valued Yoneda functor then recovers
the scheme morphisms. The natural multiplicative coordinates of the preceding
`SemidirectProduct` module identify their underlying maps with the product
pairings `(g,1)` and `(1,h)`, and the second product projection. These formulas
hold on every test scheme over `B`.

Conjugation by `(1,h)` on `(g,1)` is the image of the original action
`a.act h g`. The proof transports the ordinary semidirect product identity
`inl_aut` through the point-group isomorphism. Both inclusions are
monomorphisms of the underlying objects over `B`, as follows by taking the
appropriate coordinate after composing with them. The acting-factor
inclusion splits the projection. The normal-factor inclusion followed by the
projection is the identity-valued morphism.

On every test scheme, a point lies in the range of `semidirectInl` if and only
if its projection is the identity. Consequently `range_semidirectInl`
identifies its subgroup-functor range with the preimage of the trivial
subgroup functor under the projection. The reverse implication reconstructs
the preimage point from its first coordinate, using the identity second
coordinate.

The inclusion of `G` is a closed subgroup when `H.X.hom` is separated; the
inclusion of `H` is a closed subgroup when `G.X.hom` is separated. Each proof
uses its retraction to the corresponding product factor: that projection is
separated by base change, and a section of a separated morphism is a closed
immersion. If both structure morphisms are affine, the semidirect product
structure morphism is affine, by base change and composition. If both are
smooth, the semidirect product is smooth, because its underlying scheme is
their actual fibre product. Finally, if `H.X` is a commutative group object,
the projection is invariant under conjugation by `semidirectInr`; applying
projection to the conjugation formula reduces this to commutativity in the
point group of `H`.

The provenance is elementary derived content from the preceding semidirect
construction, the existing actual action, and Mathlib's Yoneda, product,
separation and affine-morphism APIs. No external source theorem is asserted.
This module supplies supporting morphisms and the stated product geometry;
it does not assert dynamic representability, connectedness, a Lie-image
comparison, or the host cyclic-tail comparison theorem.
