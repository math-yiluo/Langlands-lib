# Pulling a normal-model extension to the original valuation base

This internal reduction completes the transport from an actual extension on
a finite normal model to an actual extension over the original valuation
base. It assumes normal finite-type subalgebra existence and an extension
property over normal finite-type integer algebras. It does not prove either
property or the unconditional valuation-ring extension statement.

For a `TwoAxisNormalModel M`, `totalProductMap` is the self-product map
induced by its actual total carrier comparison and the inclusion of its
ring `M.T` in the original ring `R`. `extensionPullback M E` is the actual
Library line bundle obtained by pulling a bundle `E` on that total model
product back to the original product.

`product_square` proves that this map commutes with the two canonical generic
product restriction maps and the generic self-product comparison stored by
the model. Both sides have the same two projections, by `M.genericFst`.
The canonical map on the original side is precisely the chosen pullback map
in `ValuationRingTwoAxisExtensionStatement`.

`TwoAxisNormalModel.exists_extension` assumes an actual bundle `E` on the
total model product whose canonical generic pullback is isomorphic to
`M.bundle`. It pulls `E` back along `totalProductMap`. Module-sheaf pullback
composition, the commuting product square, the assumed restriction
isomorphism, and `M.comparison` give an actual restriction isomorphism to the
original bundle `D`. This transport works for an arbitrary domain `R` and
its specified fraction field `K` in common universe `u`; the model supplies
the maps, and the transport needs no valuation hypothesis.

`NormalFiniteTypeTwoAxisExtensionProperty` defines the remaining extension
property on integrally closed domains of finite type over the integers.
It uses their canonical fraction fields, actual abelian self-products and
both actual unit axes. Its conclusion is an actual total bundle with a
module-sheaf isomorphism along the canonical generic restriction map.
These finite-type rings are noetherian. This proposition is defined here
as an explicit assumption and is not proved.

`valuationRingTwoAxisExtension_of_normalFiniteType` assumes both this
property and `NormalFiniteTypeSubalgebraStatement`. A valuation domain is
integrally closed. `exists_twoAxisNormalModel` therefore supplies an actual
normal finite model of the generic bundle and both axis trivialities. The
finite-type extension assumption applies to this model. The preceding
transport gives exactly the conclusion of the published valuation-ring
statement, for its original chosen field and its canonical product map.
No rank condition on the valuation domain, including the field case, is
added.

The provenance is an internal composition of the model construction, the
Library's actual self-product maps and module pullbacks, and Mathlib's
pullback projection equations and finite-generation interface. No new
literature translation or unconditional extension theorem is asserted.
