# Galois–Cartan reduction of analytic étale local acyclicity

`HasPointedEtaleGaloisRefinements` is the supplied geometric premise.
For an arrow of ordinary étale objects and a chosen point over the
marked point of its target, it asks for a relative finite Galois germ
cover factoring through that arrow. The target is a pointed
neighbourhood with cofinal base-open inverse images. The cover source
has the same cofinality property and is distinguished over the ambient
base.

Represent a section germ in the quotient of a short exact sequence by
a section at one neighbourhood stage. Local surjectivity of the
epimorphism gives a covering image sieve. Point lifting selects an
arrow in this sieve through the marked point. The geometric premise
then gives a relative Galois cover factoring through the arrow. The
local section lift restricts to a representative at a common
distinguished stage, where it maps to the augmented germ. This gives
the local lifting field of a Galois–Cartan system on the pointed
neighbourhoods.

On a Hausdorff base with the continuous topological group action and
the admissible refinements of the local acyclicity statement, the
coinduced fixed-section hypothesis gives acyclicity for every cover in
that system. The identity base object gives the ordinary point germ by
pullback along the base opens. The Galois–Cartan theorem and the
ordinary point comparison then give vanishing of all positive
ordinary higher direct images for the restricted sheaf.

This internal reduction implements the passage from finite Galois germ
cohomology to ordinary higher direct images used in Berkovich's
equivariant étale manuscript, Proposition 1.5.1, proof step (1′),
printed page 11. It uses pointed Galois refinement as a premise.
