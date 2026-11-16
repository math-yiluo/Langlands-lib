# Relative maximal tori and the derived subgroup

This internal support module works over an arbitrary scheme. Let `G` be
reductive and let `d : D ⟶ G` be a closed normal inclusion with `D` reductive,
semisimple geometric fibres, and a specified fppf quotient of `G` by its full
range which is a relative torus. Given a closed relative torus `t : T ⟶ G`
maximal on every residue fibre, the whole scheme-theoretic intersection
`T ∩ D` is a relative torus and its inclusion into `D` is closed and maximal
on every residue fibre. The required monomorphism instance for `d` follows
from its closedness.

`relativeDerivedMaximalTorusIntersection` constructs this actual commutative
torus and its inclusion in `D`, together with these properties and equality of
its range with the first projection of the oppositely ordered pullback `D ∩ T`.
The equality compares full subgroup functors on every test scheme.

The implemented proof first observes that any closed perfect subgroup
containing all commutators is the actual derived subgroup. At every supplied
field point, published reflection and base-change results make the fibre of
`D` semisimple; published semisimple perfectness and commutator containment for
a relative-torus quotient then identify its inclusion with the actual derived
subgroup. The published field theorem on the full derived intersection gives
maximality there. The canonical pullback base-change isomorphism transports
this to maximality of the actual intersection on each residue fibre.

Published normal-intersection smoothness proves smoothness of `T ∩ D` over
the original base. The intersection is closed in the relatively affine torus,
so it is relatively affine. Its geometric fibres are tori by the same field
argument and hence connected reductive. Thus the actual commutative
intersection is reductive. The commutative-reductive relative-torus theorem
proves its étale-local splitness. Finally pullback symmetry identifies its
range with the projection used in the host correspondence statement.

All content is derived internally from the imported results. This module
establishes the forward maximal-torus intersection assertion. Isogenies,
inverse torus correspondence, uniqueness and parabolic assertions of the
host target remain separate obligations.
