# Absorbing an acting group into an ordered factor

This is an internal construction over an arbitrary base scheme and universe.
A group scheme `K` acts on `G` and on every member `H i` of a finite ordered
family. The group scheme homomorphisms `j i : H i ⟶ G` intertwine the actions
on every test scheme. A chosen index `p : Fin n` specifies the factor which
will absorb the acting group.

`absorbedSemidirectFamily` replaces `H p` by its actual semidirect product with
`K`, retaining every other factor and the original order. The normal and acting
coordinate constructions give `absorbedSemidirectPointsEquiv`: on every test
scheme, points in the new family correspond to a family of normal points and
one acting point. This is an equivalence of sets; the normal projection of a
semidirect product is not asserted to preserve multiplication.

`absorbedSemidirectMap` maps the chosen factor by the equivariant semidirect
homomorphism and maps each remaining factor through `j i` and the ambient
normal-factor inclusion.

The private group calculation multiplies pairs whose acting coordinate is
the unit except at the chosen index. The result is the product of the normal
prefix through that index, times the given acting point's action on the normal
suffix; its acting coordinate is the given point. It is proved by induction on
the number of factors and the position of the chosen index.

`absorbedSemidirectCoordinatesInv_map_points` evaluates every canonical factor
map on reassembled coordinates. `orderedPoints_absorbedSemidirectCoordinatesInv`
then applies the multiplicative semidirect coordinate equivalence to the ordered
point product and uses the private group calculation. The resulting formula is
the prefix through `p`, followed by the acting coordinate acting on the suffix,
with the original acting coordinate retained.

`lift_semidirectOrderedMultiplication` evaluates the existing scheme insertion
map at arbitrary normal and acting coordinates. Precomposition commutes with
each finite product and with the action, so its value is the same formula.
`absorbedSemidirectSchemePointsEquiv` reassembles the original normal family into
its finite product scheme and pairs it with the acting point.

The final theorem `isIso_orderedMultiplication_absorbedSemidirect` assumes that
the original morphism `orderedMultiplication j` is an isomorphism. The existing
`isIso_semidirectOrderedMultiplication` makes the insertion map at cut
`p.val + 1` an isomorphism. On every test scheme, the original ordered
multiplication for the absorbed factors is the composite of the coordinate
bijection and postcomposition with that insertion isomorphism. The all-test
Yoneda criterion therefore proves that this original ordered multiplication is
an isomorphism of schemes over the base.

All these constructions allow an arbitrary base scheme, universe, actions and
chosen position. The chosen index requires a nonempty family for this absorption
lemma. They require neither fields nor smoothness nor connectedness; they retain
all-test equivariance and the original ordered multiplication isomorphism as
premises. The provenance is internal: this is an assembly from the actual
semidirect map, finite-product coordinates and the previously constructed
semidirect insertion morphism. No semigroup realization, solvable decomposition,
scalar descent or proof of `SemigroupOrderedProductStatement` is supplied by
this unit.
