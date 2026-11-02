# The presheaf of actual automorphism isomorphisms

This internal construction uses the published coherent isomorphism pullback
for a category-valued pseudofunctor. `automorphismIsoPresheaf` assigns to
every morphism into the family base the actual automorphism isomorphisms
of its pullback. Restriction is the coherent `pullIso` with both endpoint
maps equal. The identity and composition laws are the corresponding
published pullback laws, with no quotient or truncation.

When every fibre is a groupoid, `presheafHomAutomorphismIso` identifies this
presheaf with the full endomorphism presheaf `F.presheafHom ξ ξ`. A morphism
is sent to its associated isomorphism and the inverse forgets to the
forward morphism. The naturality proof compares forward morphisms, for
which coherent isomorphism pullback is precisely the existing `pullHom`.
This enables using actual smooth automorphism representatives without
changing the automorphism data in the arrow-kernel construction.
