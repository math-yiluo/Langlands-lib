# Descent of model comparisons along valued-field extensions

This internal construction applies to arbitrary fields `K` and `L` in a
common universe `u`, a field algebra `K → L`, and valuations `vK` and
`vL` related by `Valuation.HasExtension vK vL`. Their ordered value
groups may have independent universes. Let `M` and `N` be supplied
integral models over `vK.integer` of actual groups `G` and `H` over `K`.
All scalar maps are the canonical valuation-integer maps associated to
the given field algebra.

There is no algebraicity, finite-degree, discreteness, completeness,
characteristic, reductivity or smoothness assumption. There is also no
separate flatness, surjectivity or Cech compatibility premise.

## Actual extension types

`Hom.valuationCoefficientEquiv` is an equivalence between extensions
`M.Hom N f` of a prescribed generic morphism `f : G ⟶ H` and extensions
of its scalar extension between the actual coefficient-base-changed
models. Its forward underlying morphism is exactly coefficient pullback,
as recorded by `Hom.valuationCoefficientEquiv_apply_hom`.

The published valuation-integer fpqc construction supplies the flatness
and surjectivity instances. The generic-coefficient descent construction
then supplies automatic canonical compatibility, descent, recovery and
the inverse laws for the Hom equivalence.

`Iso.valuationCoefficientEquiv` gives the corresponding equivalence for
a prescribed generic isomorphism `f : G ≅ H`. The forward map is exactly
`Iso.baseChangeCoefficients`, and the inverse is
`Iso.descendFromCoefficients`. Both inverse laws use generic rigidity:
two compatible model isomorphisms have identical forward maps, hence are
equal as isomorphisms and as model-isomorphism records.

`Iso.valuationCoefficientEquiv_apply_iso` identifies the entire forward
isomorphism with the original coefficient pullback.
`Iso.baseChange_valuationCoefficientEquiv_symm` proves exact recovery of
the supplied upstairs group-scheme isomorphism after descent.

## Original images and provenance

`integralPoints_eq_of_valuationCoefficientIso` applies the inverse
equivalence to an upstairs isomorphism extending the generic identity.
The descended isomorphism retains the original generic identifications,
so `Iso.integralPoints_eq` identifies the original two subgroup images
inside `rationalPoints G`.

This is an internal combination of `GenericCoefficientDescent`,
`GenericRigidity`, `ValuationIntegerCover` and the original model-image
transport. It removes the cover and compatibility inputs from the
model-descent application to valued fields. An upstairs extending
morphism or isomorphism is still an input: this construction does not
establish its existence or construct the model/building comparison
required by `BuildingComparisonStatement`.
