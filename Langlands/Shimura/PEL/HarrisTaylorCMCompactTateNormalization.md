# Tate-normalized representatives at arbitrary compact Harris levels

For a pointed Harris representative over a connected admissible base,
`HarrisCompactTateNormalized` requires the intersection lattice of its
original level orbit to equal the image of the full integral Tate group
inside the rational Tate module. The intersection uses the fixed source
span and all frames in the orbit, as in `HarrisCompactOrbitLattice`.

At an algebraically closed point of characteristic zero,
`exists_harrisCompactTateNormalized` replaces a representative
satisfying the determinant and dimension condition by one satisfying
that condition and the lattice equality. Both represent the same
pointed numerical CM class. The proof applies
`commensurableInvariantLatticeRealization` to the intersection, using
its monodromy invariance and integer bounds. The finite-set affine
neighbourhood hypothesis follows from the representative's actual
polarization by `DualWitness.forall_finset_fibre_affine` and
`properFibreAmpleAffineOpen`. The resulting isogeny model carries the
conjugate action and an actual polarization. Transport of the orbit
and its lattice identifies the new lattice with the full integral Tate
image of the model. The model isomorphism and its multiplier witness
equality of the classes.

`harrisCompactTateNormalized_iso_integral` starts with two such
lattice equalities at the same point and a rational equivariant
isomorphism satisfying the polarization and orbit equations. Its
rational Tate map preserves and reflects membership in the two
intersection lattices. These are the full integral images by
normalization, so the forward and inverse maps satisfy the two
hypotheses of `connectedIntegralLatticeReflection`. The theorem gives
an actual isomorphism with the original forward and inverse rational
arrows.

This is an internal application of the compact orbit lattice, the
existing Harris isogeny model, and the generic Tate lattice realization
and integral reflection theorems. It uses the original level and the
original equivalence of representatives.
