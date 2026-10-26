# Actual factor filtrations in external tensor products

This internal adapter specializes the indexed tensor filtration to the actual
external tensor action of a family of groups. It starts from a supplied
filtration of one original factor. It provides no representation-specific
filtration or classification result.

`externalSlotFiltration ρ j s` first pulls the supplied filtration `s` back
along the coordinate homomorphism from the original product group to `H j`.
It then applies `slotFiltration` to the original coordinate actions. Its
ambient representation is precisely `FiniteTensor.external ρ`, and its steps
are actual invariant subspaces, with the same length and endpoints as `s`.

`externalSlotFiltrationGradedEquiv` identifies its actual successive quotient
with the tensor of the original complement actions and the original quotient
of `s`, all pulled back through their original coordinate homomorphisms.
The comparison composes the indexed tensor graded equivalence with
`ObjectRepFiltration.compGradedEquiv` in the quotient slot.

`externalSlotFiltrationGradedEquivOfFamily` accepts actual equivalences in each
complement factor and from the actual slot quotient to the supplied replacement
factor. Pulling these equivalences through the coordinate homomorphisms and
applying the indexed replacement construction gives an equivalence with the
actual external tensor of the replacement family.

`externalSlotFiltrationGradedMap` makes the same construction when the map from
the actual slot quotient is an arbitrary intertwiner.
`externalSlotFiltrationGradedMap_injective` proves its injectivity from that of
the supplied factor map: coordinate pullback keeps the linear map, the quotient
comparison is an equivalence, and the indexed tensor injectivity theorem
applies over the coefficient field.

The index type, coefficient field, group carriers and both factor carrier
universes are independent. No finite index, simplicity, nonzero layer or finite
dimension hypothesis occurs. A specified slot is required; a singleton index
and zero-length supplied filtration are allowed with the usual endpoint
conditions. Smoothness is not required for these algebraic constructions.
For finite index types, the existing `isSmooth_external` supplies ambient
smoothness from smooth original factor actions.

The provenance is internal: this module assembles `FiniteTensor.external`,
the supplied-filtration constructors and graded maps from
`Tensor.FiniteFiltration`, and the coordinate pullback and actual quotient
comparison from `Filtration.ObjectTransport`. Equivariance of each pulled-back
map is its original intertwining identity at the relevant coordinate.
