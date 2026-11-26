# Compact-finite vectors in the closure of an admissible subspace

`AdmissibleCompactFiniteClosureStatement` concerns a jointly continuous Banach representation
and a compact subgroup with normalized left Haar measure. Let `W` be a compact-invariant
algebraic subspace whose vectors are compact finite and whose spaces of intertwiners from
continuous finite-dimensional compact representations are finite dimensional. Every
compact-finite element of the norm closure of `W` belongs to `W`. The ambient representation
may have arbitrary compact multiplicities.

`admissibleCompactFiniteClosure` proves this extension of the compact averaging argument in
`CompactFiniteClosure`. A weight in a fixed finite translation type defines a compact
intertwiner by weighted integration of an orbit. On input from `W`, its image lies in the
finite-dimensional orbit span of that input, since the integrand lies in this closed subspace.
The intertwiner therefore takes values in `W`. At a fixed weight coordinate, its value lies
in the evaluation image of the corresponding intertwiner space into `W`. Admissibility makes
this image finite dimensional and therefore norm closed. Continuity of the average extends
the inclusion in this image to all inputs from the closure of `W`.

The compact-finite vector has a finite-dimensional compact orbit span contained in the norm
closure of `W`. The inverse-action coordinates of this vector and each basis vector of its
orbit span give the compact averages in `sum_compactReconstructionWeight`. By the previous
argument all these averages belong to `W`. Their sum is the original vector.

This is an internal consequence of compact averaging and finite-dimensional closedness.
It allows the completion of an admissible algebraic image to recover its compact-finite
vectors inside a Banach target whose own compact multiplicities may be infinite.
