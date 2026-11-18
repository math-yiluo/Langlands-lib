# Exact affine formulas for the odd subgroup constructions

The module transports the all-test formulas of the actual short and even
subgroup maps to the original coefficient algebra of an affine test.
The scalar matrix chart commutes with the canonical affine global-sections
isomorphism. The same isomorphism transports the sole coordinate of the
constructed additive affine point to its specified scalar.

Consequently `shortMap` applied to that additive point has exactly
`shortMatrix a c` as its coefficient matrix. The image of an even orthogonal
affine point under `evenMap` has exactly the determinant-corrected block
matrix `diag(det g,g)` over its original coefficient algebra. These formulas
include all commutative coefficient algebras and nonreduced tests.

This is an internal affine-coordinate adapter for the previously constructed
actual morphisms, using the corepresented affine/global-sections comparison.
No new literature translation or structural group assertion is introduced.
The field has arbitrary universe `u`, and the finite hyperbolic index lies
in `Type`.
