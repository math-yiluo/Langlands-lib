# Finite products of coactions

This internal construction equips a finite product of copies of an actual
`GroupoidCoaction t M` with the coordinate coaction. Rings have arbitrary universe
`u`, the module has universe `v`, and the finite index type is in `Type` (universe zero).
A `Fintype` and decidable equality on the index type are explicit. No étaleness,
flatness, or Noetherian hypothesis is needed.

`piRight_apply_eq_lTensor` identifies each coordinate of Mathlib's finite-product
tensor equivalence with tensoring the coordinate projection.
`finitePi_tensor_ext` consequently checks equality of tensors on their coordinates.
`finitePiCoactionMap` applies the inverse equivalence to the tuple of the original
coaction values. Its projection identity proves target semilinearity and transports
the counit and coassociativity laws coordinatewise. The latter uses
`coactionCompose_map` for the additive coaction before the product coaction has
been constructed. The resulting actual coaction is `finitePi`.

The coordinate projections and the constant-family diagonal are equivariant.
Choosing one index makes the former a left inverse of the latter. The existing
cohomological retract lemma then proves
`oneCohomologyVanishes_of_finitePi`: degree-one vanishing for a nonempty finite
product implies degree-one vanishing for its coefficient coaction. The conclusion
uses the Library's `OneCohomologyVanishes` predicate. This helper supplies no
geometric acyclicity theorem or assertion for an empty product.
