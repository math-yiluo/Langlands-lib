# Vanishing group cohomology on a finite Galois germ

The diagram has a cofiltered index and consists of distinguished étale
stages over one analytic base, with natural deck automorphisms from a
finite group. Each stage contains a point above the chosen base point.
The geometry is supplied as ordinary point lifting along covering
sieves, compact quasi-étale action lifts, transitivity on the topological
fibres, freeness on the `L`-points, and cofinal open restrictions of each
stage. The acting group `G` is topological, and its lift system has
admissible refinements. `galoisStageSections` gives the representation
diagram for a given étale G-sheaf `S`, with inverse deck action and
ordinary restriction maps.

The vanishing theorem requires `HasCoinducedGaloisFixedSections L S`.
The proof chooses finitely many local restrictions that cover after
shrinking the base. At a smaller stage identified with such an open
restriction, the finite family of cochain coordinates consists of
sections discrete for its lift. They lie in a common fixed
subrepresentation. The coinduction hypothesis supplies bijective
coordinates on the fixed subrepresentation, so its positive deck
cohomology vanishes. The filtered-colimit criterion gives vanishing in
every positive degree for the colimit of the section representations.

This internal computation supplies the group-cohomology term required in
the Galois germ argument of Berkovich's equivariant étale manuscript,
Proposition 1.5.1, proof step (1′), printed p. 11. The geometry of the
diagram and the comparison with right derived ordinary direct images are
further inputs to that argument.
