# Pullback of a supplied parabolic representing scheme

This internal derived construction transports a supplied representation of the
actual parabolic presheaf along any morphism `b : S' ⟶ S`. It does not establish
the existence of a representation.

For a reductive group scheme `G` over `S`, a parameter scheme `M : Over S` and
an equivalence `e` representing `parabolicPresheaf G hG` by `M`,
`representableByBaseChange b hG e` represents the actual parabolic presheaf of
the pulled-back group by the actual scheme `(Over.pullback b).obj M`.
The slice adjunction identifies maps to that pullback with maps to `M` over
`S`. Composing with `e` gives a representation of the restricted presheaf.
The canonical natural isomorphism `parabolicPresheafBaseChangeIso` then
identifies this with the actual parabolic presheaf over `S'`. Naturality follows
from the slice adjunction and the supplied representation.

`representableByBaseChange_homEquiv` states the resulting parameter formula:
after the canonical direct/iterated ambient comparison, the parameter evaluates
by `e` at its adjoint map to `M`. Thus this transports actual subgroup functors
with their specified ambient pullbacks.

`exists_smooth_proper_representation_baseChange` retains smoothness and
properness of the structure morphism, using their stability under scheme
pullback. No restriction on `b` is imposed. Every conclusion remains
conditional on a supplied representation over `S`; the unconditional target
`RelativeParabolicSchemeStatement` is still a separate obligation.

The provenance is internal: the construction uses the slice adjunction, the
imported comparison of actual parabolic presheaves and pullback stability of
smooth and proper morphisms. No new external mathematical assertion is used.
