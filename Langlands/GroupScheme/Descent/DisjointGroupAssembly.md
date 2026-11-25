# Assembling group schemes over a finite disjoint decomposition

This internal construction assembles a finite family of group schemes over
the respective components of a disjoint decomposition of a base scheme.
It is motivated by the finite disjoint-union Weil presentation in Brian
Conrad, *Reductive group schemes* (2014), Proposition 6.4.4 and Remark 6.4.5,
pp.232–233, registered as `conrad-2014-reductive-group-schemes`.

The base decomposition is supplied by morphisms `p i : Z i → S` such that
the induced morphism from the coproduct of the `Z i` is an isomorphism.
The construction allows any finite index type in the arbitrary universe
`u`, including the empty type.

The underlying scheme is the coproduct of the component groups, with the
induced map to `S`. The van Kampen property of finite coproducts in the
category of schemes proves that its pullback to each `Z i` is the original
relative component. The published fully faithful restriction functor on
slice categories then transports the pointwise group object on the
family to a group object over `S`.

This is an internal categorical assembly construction. It neither imposes
reductivity nor assumes affineness of the component groups. The later
finite-product algebra and Weil-restriction comparisons are separate
steps.

`group p H` chooses the resulting group scheme. `componentIso` identifies
its actual base change along each `p i` with `H i` as a group scheme.
`underlyingIso` identifies its relative underlying scheme with the supplied
coproduct over `S`; this is an isomorphism rather than a definitional
identity. In particular, the assembled scheme is affine when each
component scheme is affine, using finiteness of the index type.
