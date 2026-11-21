# Acyclicity on relative finite Galois germs

For a Hausdorff analytic base with a continuous action of a topological
group, take an étale G-sheaf with admissible refinements and
`HasCoinducedGaloisFixedSections`. Each supplied relative
`EtaleGermGaloisCover` then has vanishing positive deck cohomology on
the ordinary restriction of the sheaf. The representation is that of
the cover germ, with inverse deck pullback.

Take the finite family of coordinates of a cochain at a distinguished
stage. The intersection of their discrete sieves is covering.
Point lifting gives one ordinary arrow in that intersection through
the chosen point. Its image is open, and cofinality of inverse images
of ambient neighbourhoods makes this image contain the whole stage
after a smaller base restriction. The pointwise lifting result gives
a covering pullback sieve there.

Both stages have action lifts by the compact quasi-étale lift theorem
and its distinguished restriction. Finite-cover descent makes the
restricted coordinates discrete for the smaller lift. The deck group
acts freely on `L`-points there because the action commutes with the
inclusion into the original Galois cover. The coinduction hypothesis
therefore puts the coordinates in one acyclic subrepresentation.
The filtered-colimit criterion proves the vanishing, and the
equivariant comparison carries it to the Cartan cover functor.

This is the relative version of the finite deck calculation in
Berkovich's equivariant étale manuscript, Proposition 1.5.1,
proof step (1′), printed page 11.
