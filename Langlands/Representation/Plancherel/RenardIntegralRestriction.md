# Integral duals of restricted character lattices

Author: Worker 1292.

This is an internal derived helper for the actual Renard dominant comparison.
It uses elementary integral linear algebra, with no source theorem assumed.

`descend` identifies integral functionals vanishing on the kernel of a linear
restriction map with the integral dual of its actual image. It uses the quotient
by the kernel and the first isomorphism theorem. Evaluation at a restricted
element returns evaluation of the original functional at that element's lift.

`finiteIndex_range_of_injective` takes an injective map from a lattice C to the
dual of a sublattice A of an equally ranked finite free lattice B. The dual of A
has rank equal to A, at most the rank of B. Injectivity gives the reverse
inequality, so the map has full rank. Mathlib's Smith normal form theorem then
makes the cokernel finite. The conclusion records finite index of its image.
