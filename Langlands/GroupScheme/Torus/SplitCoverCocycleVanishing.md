# Cocycles over a finite Galois splitting cover

This derived internal module combines the actual Galois tensor-point comparison,
the finite-unit vanishing theorem, and free-tensor stability of Tate cohomology.
All fields and coefficient objects have arbitrary common universe `u`; the
scalar ring is `ULift.{u} ℤ` with the ordinary integral action.

`latticeRepresentation_free` uses the actual splitting isomorphism to identify
the transported cocharacter lattice with that of a coordinate split torus.
The published coordinate equivalence identifies this module with a finite
product of copies of the lifted integers. Transporting freeness back along
these linear equivalences proves that the actual cocharacter representation
has a free underlying module; no triviality of its Galois action is required.

`pointRepresentation_H1_isZero` assumes the finite-extension norm criterion
`HasDimensionLEOne k` and a finite Galois extension `L/k` over which the actual
commutative base change is split. The actual field-unit representation is
cohomologically trivial. The free cocharacter factor is flat, so the proved
free-tensor vanishing argument gives zero Tate cohomology of their diagonal
tensor product in degree one. Transport along `tensorPointIso` gives the same
vanishing for the actual coefficient-point representation. The comparison
between positive Tate cohomology and ordinary group cohomology gives the
stated ordinary degree-one vanishing.

`cocycle_isTrivial` applies the proved ordinary-H1 bridge to an actual scheme
cocycle. Its witness lies over the original splitting cover `Spec L`, and the
coboundary identity holds on every relative test scheme, as required by the
original `Cocycle.IsTrivial` definition. This module still assumes the chosen
finite Galois cover splits the group; the unrestricted torus-cocycle statement
and Steinberg quasi-splitness require further work.

`cocycleTrivializingPoint` constructs an actual point on that original cover
by choosing the witness of `cocycle_isTrivial`. Its specification
`cocycleTrivializingPoint_spec` is the all-test coboundary identity supplied
by that existential proof. The choice adds no vanishing hypothesis or
new cover.
