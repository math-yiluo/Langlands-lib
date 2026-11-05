# An actual Picard family realizing a finite tangent basis

This internal construction specializes the actual weighted first-order family
to a finite basis. Its inputs are a commutative ring `k`, a field `k`-algebra
`K`, an actual proper scheme morphism `f : X ⟶ Spec k`, and an actual line
bundle `M` on its relative residue scheme. All rings, schemes and the finite
basis index retain the arbitrary common universe `u`.

For any finite index type `ι` in that universe and any basis `b` of the actual
pointed dual-number classes, `family_basis_weighted` identifies the pointed
class of the actual restriction of `FiniteTangentFamily.family f M b`
along `FiniteTangents.weighted k K c` with `b.equivFun.symm c`.
The weighted restriction theorem gives the linear combination of the basis
vectors, and the inverse coordinate formula for a finite basis gives the
displayed equality. The weighted test arrow is literally
`(a,w) ↦ (a, ∑ i, c i * w i)`.

`basisFamily_bijective` states that coefficient vectors classify these
actual pointed restriction classes. Its proof identifies the entire
restriction function with the inverse basis coordinate equivalence and uses
that equivalence's bijectivity. `basisFamily_existsUnique_parameter` states
that every actual pointed dual-number deformation object is isomorphic to
one of the restrictions, for a unique coefficient vector. The coordinates
of its pointed quotient class give the required vector. The restriction
formula gives equality in the isomorphism quotient, which supplies a
nonempty actual pointed isomorphism. Injectivity of the coordinate
equivalence gives uniqueness of the vector. Uniqueness of the isomorphism
is not asserted.

The published theorem
`ArtinianDualNumberComparison.finiteDimensional_classes` proves that the
actual pointed dual-number classes at `M` are finite dimensional over `K`.
`Index` is the universe lift of `Fin` of their dimension, and `basis`
reindexes `Module.finBasis` by that lift. Dimension zero is allowed. No
projectivity, smoothness or condition on global functions is added.

`test` is the actual augmented Artinian test `K ⊕ K^Index`, with square-zero
second summand. `family` is the actual pointed line bundle obtained from
`FiniteTangentFamily.family` applied to `basis`. Its specified residue
identification is part of the original actual deformation object.
`parameter c` is the actual weighted test arrow for a coefficient vector.
`parameterLinearEquiv` records the inverse coordinate linear equivalence.
`family_weighted` specializes the weighted restriction formula to this
chosen finite basis, and `existsUnique_parameter` specializes the actual
pointed-isomorphism existence and unique-vector result. These statements
write the original actual family and weighted-arrow expressions explicitly.

The derivation uses the actual first-order class finiteness theorem, the
previous actual weighted family and finite-dimensional basis identities.
It classifies restrictions along the displayed weighted, `K`-linear
parameter arrows. It does not claim that every augmented `k`-algebra arrow
from the parameter test to the dual numbers has this form. No higher-order
lift, complete local hull, formal versality, algebraization or smooth atlas
is constructed here.
