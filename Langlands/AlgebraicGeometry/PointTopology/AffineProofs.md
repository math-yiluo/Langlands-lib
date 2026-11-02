# Finite-coordinate affine topology proofs

Author: Worker 105.

Proofs for Brian Conrad, *Weil and Grothendieck approaches
to adelic points* (December 31, 2011), Proposition 2.1, printed page 2.
Registered source `conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

The implemented proof factors a finite generator evaluation through the
surjective polynomial presentation. Precomposition with a surjective algebra
map is an embedding: a choice of preimages gives a continuous reindexing of
the full function spaces. If the value ring is Hausdorff, its image is the
intersection of the closed conditions that every element of the kernel maps
to zero. Mathlib's algebra-homomorphism descent through a surjection supplies
the reverse inclusion. This part uses no continuity of ring operations.

Polynomial points are homeomorphic to arbitrary tuples by evaluation on
variables and the inverse polynomial evaluation map. Continuity of the inverse
follows by polynomial induction, using constant coefficients, addition and
multiplication. Only the value ring has a topology.

The finite-coordinate proofs use the surjection from multivariate polynomials
given by any generating family. They compose its point-space embedding with
the polynomial point homeomorphism. Closedness uses all kernel equations,
so no finite-presentation hypothesis is required. The case of zero generators
is included.

For local compactness, Mathlib's finite-type characterization supplies a
surjective map from a polynomial ring in finitely many variables. The point
space is therefore a closed subspace of a finite product of the Hausdorff
locally compact value ring. The final theorem proves the aggregate
`AffineCoordinateProperties` target without any topology on the base ring or
the coordinate algebra.

The theorem proves the published `AffineCoordinateProperties` target.
Products, fibre products, axiomatic uniqueness and the remaining whole-paper
assertions are separate obligations.
