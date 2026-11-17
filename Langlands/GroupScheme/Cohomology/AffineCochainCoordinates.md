# Coordinate modules of regular cochains on affine groups

Let `R` be a commutative ring, `H` an affine group scheme over `Spec R`, and
`M` any `R`-module. This internal construction identifies the regular cochains
of `RegularCochains` with their values at actual universal points of the
chosen affine presentation of `H`. No finiteness, freeness, flatness or
projectivity is assumed for `M`, and `H` need not be smooth or flat.

`genericPoint` is the point corresponding to the identity homomorphism of
`Lie.coordinateAlgebra H`. `pointSpecialization` is the coordinate-algebra
homomorphism corresponding to a supplied actual point. The specialization
lemmas state that it takes the generic point to that point and commutes with
arbitrary changes of test algebra.

`oneCochainCoordinateEquiv` gives an equivalence of underlying sets between
regular one-cochains and `coordinateAlgebra H ⊗[R] M`. The inverse specializes
the tensor along the coordinate homomorphism of each actual point. Naturality
of a cochain proves that it is recovered from its value on the generic point.

`pairCoordinateAlgebra` is the tensor square of the source coordinate algebra.
Its two generic points are induced by the two tensor inclusions.
`pairSpecialization` sends these points to any prescribed pair, with the
expected pure-tensor formula and naturality. These properties give
`twoCochainCoordinateEquiv`, an equivalence of underlying sets between regular
two-cochains and `pairCoordinateAlgebra H ⊗[R] M`.

The final three lemmas reduce the one-cocycle equation and the one- and
two-coboundary formulas to the corresponding universal point or generic pair.
A one-coboundary primitive remains an actual base-module element; a
two-coboundary primitive remains a natural one-cochain on all affine tests.
The proofs apply the coefficient map along specialization and use the
naturality of the cochains and representation. The extensionality lemmas for
one- and two-cochains are also supplied, independently of source affineness.

These are consequences of affine representability and tensor functoriality in
the project's existing cochain interface. They do not prove cohomology
vanishing, a geometric reduction-kernel comparison, or any infinitesimal
lifting theorem. No criterion for the two-cocycle equation at a generic triple
is asserted here.
