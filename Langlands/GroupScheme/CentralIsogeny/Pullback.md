# Central isogenies in Cartesian squares

`IsCentralIsogeny.of_isPullback` proves stability of a central isogeny under a
Cartesian square of group schemes over the same arbitrary base. The hypothesis
is a pullback square of their underlying schemes over that base.

This is an internal consequence of the published definition of a central
isogeny, stability of finite, flat, surjective and locally finitely presented
scheme morphisms under pullback, and the all-test-scheme characterization of
the full kernel. It introduces no additional geometric assumption.

For centrality, a point killed by the upper horizontal map has central image
under the left vertical map, since that image is killed by the lower central
isogeny. Its upper horizontal image is the identity. Consequently its
commutator with every point has equal images under both projections of the
pullback. Joint monicity gives equality of the two products. The proof makes
this argument after every restriction of test schemes.
