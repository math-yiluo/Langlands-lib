# Actual affine group points over a family of coefficient rings

For a commutative base ring `R`, an affine group scheme `G` over `Spec R`,
an indexing type `J` in the base universe, and a dependent family of commutative
`R`-algebras `A i`, this internal derived construction identifies the existing
actual point group `G(Π i, A i)` with `Π i, G(A i)`. The index type need not be
finite or nonempty.

`affinePointsEval` is induced by the unital coefficient evaluation algebra map.
`affinePointPi` assembles the coordinate-algebra homomorphisms of the given
points using `AlgHom.pi`, then applies the inverse of the existing affine
scheme/global-section point equivalence. `affinePointPi_evaluation` and
`affinePointsEval_evaluation` identify the values of every global regular
function in these constructions. Injectivity of all regular-function
evaluations proves both inverse laws. Coefficient extension preserves the
original point group operations, so `affinePointsPiEquiv` is a multiplicative
equivalence for those groups.

When every coefficient algebra has any topology, the product coefficient
algebra has the product topology. Each projection is continuous by the existing
coefficient-map continuity result. Assembly is continuous because every global
regular-function evaluation has continuous components. Thus
`affinePointsPiHomeomorph` preserves the existing evaluation topologies.
No continuity of the coefficient ring operations or algebra maps, finite type,
Hausdorffness, local compactness or reductivity is required.

The provenance is the universal property of dependent products of algebras,
implemented using pinned Mathlib's `Pi.evalAlgHom` and `AlgHom.pi`, and the
existing affine scheme/global-section equivalence. It extends the binary
coefficient-product construction to dependent products. It assigns no manifold
structure or measure and proves no restricted-product or reduction theorem.
