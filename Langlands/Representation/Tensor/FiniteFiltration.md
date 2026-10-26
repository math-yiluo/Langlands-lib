# Actual filtrations in one indexed tensor slot

This internal construction lifts a supplied filtration in one factor to the
actual indexed tensor product. It uses the published factorwise action
`FiniteTensor.action`, binary tensor filtrations, and object-filtration
transport. It supplies no representation-specific filtration or classification
theorem.

`congrEquiv` applies a family of actual equivariant linear equivalences to
Mathlib's indexed tensor product. Its pure-tensor formula and equivariance
follow from the corresponding factor formulas.
`slotEquiv ρ j` identifies the actual indexed action with the binary tensor
of the action on the complement of `{j}` and the action in slot `j`.
The underlying linear equivalence is Mathlib's
`PiTensorProduct.equivPiTensorComplSingletonTensor`; equivariance is checked
on pure tensors. The stated pure-tensor formula fixes its orientation.

`slotFiltration ρ j s` tensors the supplied filtration `s` on the left by
the actual complement tensor representation. It then uses the inverse of
`slotEquiv` to transport that binary image filtration back to the original
indexed tensor. Thus its steps are actual invariant subspaces of that tensor
and it has the same length, order, and zero and full endpoints as `s`.

`slotFiltrationGradedEquiv` first undoes transport on the actual graded
quotient and then applies the published binary tensor graded equivalence.
Its target is the actual complement tensor representation tensored with the
original actual quotient of `s`.
`slotFiltrationGradedEquivOfFamily` composes this with supplied equivalences
in the quotient slot and each complement slot, and then reassembles a supplied
indexed family using the inverse slot splitting.

`slotFiltrationGradedMap` performs the same construction with an arbitrary
actual intertwiner from the original quotient in slot `j`.
`slotFiltrationGradedMap_injective` proves that this map is injective when
the supplied slot map is injective: tensoring that map with the complement
equivalence preserves injectivity over a field, and both surrounding graded
and splitting maps are equivalences.

The two indexed tensor equivalences work over any commutative coefficient ring.
The filtration constructors and injectivity proof use a coefficient field.
No layer is required to be simple, nonzero, or finite-dimensional.
The filtration length may be zero. The index type, coefficient ring, group,
and the two representation families retain independent universes.
The algebraic splitting and supplied-filtration construction do not require
the index type to be finite; in particular they apply to all finite block
products. A specified slot is required, so there is no slot construction for
an empty index type. A singleton index is allowed and its complement tensor
is the usual indexed tensor over the empty family.

The provenance is internal. The construction assembles Mathlib's indexed
tensor equivalence and tensor-map injectivity with
`ObjectRepFiltration.tensorLeft`, `tensorLeftGradedEquiv`,
`LengthTwo.transport`, and `equivTransportGradedEquiv`. For external tensor products,
instantiate the common group by the product group and pull each original
factor action and the supplied slot filtration back through its coordinate
homomorphism. The separate `ObjectRepFiltration.comp` adapter provides that
filtration pullback without requiring surjectivity.
