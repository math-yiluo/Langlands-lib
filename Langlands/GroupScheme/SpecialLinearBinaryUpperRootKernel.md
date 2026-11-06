# The actual additive kernel of the binary upper-triangular diagonal character

Over every commutative base ring, `upperRootMap` factors the existing additive
upper root map through the actual upper-triangular special linear subgroup.
Its composite with the triangular inclusion is the original ambient root map,
and it is a closed immersion.

The last diagonal character has exactly this additive root subgroup as its
kernel on every relative test scheme. `diagonalKernelIso` identifies the full
scheme-theoretic kernel with the actual additive group, compatibly with its
inclusion into the triangular group. The upper root subgroup is consequently
normal on all test schemes.

This is an internal explicit matrix construction. A triangular determinant-one
matrix whose last diagonal is one also has first diagonal one, so it is the
upper transvection with its given off-diagonal coefficient. The sole additive
coordinate realizes that coefficient on the original test scheme. The
published kernel and represented-subgroup constructions turn this
pointwise comparison into an isomorphism of actual group schemes.

Parabolicity, maximality as a geometric unipotent radical, and the general local
Kneser–Tits theorem are not proved here.
