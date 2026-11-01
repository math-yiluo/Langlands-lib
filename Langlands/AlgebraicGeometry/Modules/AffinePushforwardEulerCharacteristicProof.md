# Proof of Euler invariance under actual affine pushforward

`affinePushforwardEulerCharacteristic` proves the complete proposition
`AffinePushforwardEulerCharacteristicStatement` in arbitrary universe `u`.

The helper `affinePushforwardCohomologyIso` works over any affine
commutative-ring base. For an actual affine map and actual quasi-coherent
coefficient sheaf, the published
`affineQuasicoherentHigherDirectImageVanishing` gives zero higher direct
images in every positive degree. The published
`pushforwardCohomologyIso` therefore gives an isomorphism, in each degree,
between the two actual relative cohomology modules. No vanishing or
comparison hypothesis is supplied by the caller.

Over a field, these are linear equivalences over the same field. In
both directions the proof transports finite generation through these
equivalences. It transports the same eventual vanishing bound through
the categorical isomorphisms. Finally, equality of the finite dimensions
in every degree makes the two summands defining the Euler characteristics
equal. `finsum_congr` then proves equality of the integer invariants.

This proof uses the actual derived cohomology comparison and introduces
no rank formula, numerical substitute, or polynomiality assumption.
Its provenance and its role as a finite-map cohomology prerequisite are
described in the statement's paired Markdown.
