# Projections of the local-isogeny graph

This is derived support for split isogeny realization. The groups, two possibly
different tori, local centralizers, and actual local isogenies are those of
`SplitIsogenyGraph`. The field is arbitrary. All subgroup containments are on
all scheme tests.

A morphism from a reduced group factors through a closed subgroup whenever
its composite with a surjective homomorphism does. The proof transfers the
underlying range containment through the surjective map, then uses reducedness
to obtain actual scheme factorization through the closed subgroup.

Apply this observation to each local isogeny and to the prescribed torus
isogeny. Every closed subgroup containing the second graph projection contains
each entire target centralizer and the target torus. The target centralizers
are smooth, so the required reducedness holds over arbitrary fields. No
surjectivity on points of an arbitrary test scheme is asserted or needed.

If the target directions cover the simple roots of one generic chamber, take
the actual closed image of the second projection. The preceding containment
puts the positive and negative simple-root subgroups in that image. The
explicit chamber-centralizer identity puts its middle factor there as well.
The published simple-Levi generation theorem makes the image inclusion an
isomorphism. The image quotient is flat, surjective, quasi-compact, and locally
of finite presentation, so the second projection has those properties.

The result assumes the stated coverage and chamber-centralizer identity; it
does not establish general realization or transport of simple systems through
a root-datum isogeny. The characteristic-power local factors and possibly
nonsmooth kernels are retained in the actual local isogenies.

`FaithfullyFlatLocalIsogenyGraphEnvelope` records an actual graph with both
projection geometries. Its constructor applies the first and second projection
theorems to explicit source and target coverage and chamber-centralizer data.
