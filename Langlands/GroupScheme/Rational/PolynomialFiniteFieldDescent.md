# Finite fields of definition of polynomial points

This internal supporting module keeps actual points of an affine group scheme,
over polynomial coefficient algebras, when descending to a finite intermediate
field. The target group is locally of finite type over the original field.
Polynomial variables are indexed by `I : Type`, including the finite types
used for vector groups, while the fields retain the arbitrary universe `u`.

`mapCoefficients` extends coefficients of a polynomial-valued point, leaving
all variables fixed. Successive extensions compose.

`exists_finiteDimensional_mapCoefficients_eq` assumes that the coefficient field
extension is algebraic. It takes finite algebra generators of the target
coordinate algebra and adjoins the finitely many coefficients of their
polynomial images. Algebraicity makes each coefficient integral over the base
field, so this intermediate field is finite-dimensional. Every coordinate lies in the coefficient-map range,
by induction on algebra generation. The published injective coordinate
factorization then gives an actual point over that finite intermediate field,
with its original point recovered after extension.

For a Galois extension, its finite normal closure gives a finite Galois model.
`FiniteGaloisModel` retains the intermediate field, point and exact extension
equation; `finiteGaloisModel` chooses this data.

Provenance: this is an internal assembly of affine coordinate factorization,
finite generation, finite coefficient support and finite normal closure. No
splitness or unipotence theorem is assumed or concluded.
