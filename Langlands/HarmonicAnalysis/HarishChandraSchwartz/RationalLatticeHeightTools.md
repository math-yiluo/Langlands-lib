# Height control on translated cocharacter sublattices

Author: Worker 836, Task 5326. Internal helper for the Xi upper-bound proof.

`exists_submodule_basis_coord_height` bounds the sum of the absolute integral
coordinates in any submodule of the cocharacter lattice of a split torus.
The bound is a positive constant times one plus the actual matrix height of
the uniformizer power of the submodule point plus a fixed ambient translation.
The submodule basis is chosen independently of the translation; the constant
may depend on that translation.

This is a derived consequence of the published
`exists_abs_latticePairing_le`, the perfect character/cocharacter pairing,
and Smith normal form. The helper `LatticeFaceTools.exists_basis_coord_bound`
provides ambient integral linear forms bounding the submodule coordinates.
Perfection realizes those forms as character pairings. Apply the character
height bound to the translated point and use the triangle inequality to
subtract the translation. Sum over the finitely many coordinates and enlarge
the nonnegative constant using the nonnegativity of the matrix height.

No chamber condition is imposed. In the intended face application, the
submodule is the common kernel of the simple roots in the face, and the
translation is one of finitely many representatives.

`exists_unipotent_submodule_coefficient_height` applies the algebraic uniform
degree coefficient bound to an action of this sublattice. It transports the
action through the basis to an integer coordinate lattice, applies
`unipotentLatticeCoefficientBound`, and raises the coordinate-height estimate
to the resulting natural exponent. The exponent depends on the sublattice
and the given global nilpotence exponent, and is chosen before the vector,
functional, and translation. This helper assumes the global nilpotence
condition for the supplied action; it does not prove Jacquet unipotence.
