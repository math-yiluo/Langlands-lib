# An actual numbered type-B base for the odd identity torus

Every actual root datum of the split odd identity torus has an integral
base whose simple roots are consecutive coordinate differences followed
by the final coordinate short root. Its simple coroots are the same
chain followed by twice the final cocharacter. The base has a specified
numbering, and each pairing equals the corresponding entry of Mathlib's
`CartanMatrix.B` in that order.

Each simple vector is first realized by an actual root index. The signed
root and coroot computations put all roots into the positive or negative
cone for the root chain, and all coroots into the corresponding cone for
the coroot chain. Integral independence of both families supplies the
other base axioms. These facts transfer through the actual character and
cocharacter coordinate equivalences; the integer dot-product computation
then supplies every Cartan entry.

For at least two hyperbolic indices the actual odd identity component is
connected reductive and its identity torus is split and maximal. The
published actual-root-datum existence theorem consequently gives a
reduced root datum with the constructed numbered base over every field.
The field universe and characteristic are unrestricted.

This is an internal construction from the preceding actual-root and
integral-coordinate results. The existing type-D numbered-base module
supplies a proof pattern for transporting cones and numbering finite
supports; its type-D coroot formulas are not used here. No external
translation or statement about full-group connectedness is asserted.
