# Actual polarized integral models of normalized Harris CM representatives

This is an internal construction from the existing order-model, polarized-action
and normalized Harris CM interfaces. It uses the actual universe-zero number
fields, central simple algebra and positive auxiliary involution attached to the
Harris signature charts. No new assertion from external literature is introduced.

The inputs are the existing `Prerequisites` package `P`, the full generic
`ProperFibreAmpleAffineOpenStatement`, `TorsionFiniteEtaleStatement`, an actual
`AdmissibleCMBaseCategory` object `Z`, and a `PositivePolarizedAction` `X` on
`Z.obj.left`. Thus connectedness, local noetherianity, quasi-separatedness,
the named Lie and dual prerequisites, pair additivity and dual existence are
already supplied by this particular test base. The construction does not assert
that every scheme over the CM field is admissible.

The generic geometric premise remains an explicit argument. The result does not
prove it and does not assume an integral model or a polarization on the model.

## Relative dimension on an actual integral model

`IntegralOrderModel.relativeDimension_iff_overField` applies in universe `u`
to any integral model over a scheme mapping to a characteristic-zero field
spectrum, for every specified natural relative dimension `g`. The order ring may
lie in an independent universe `v`. It does not need a polarization, determinant
condition, or CM data.

The common integer in the integral inverse data is nonzero. Its image in the
field, and hence in the global sections of the base, is a unit. The existing
`integralInverseData_finiteEtaleIsogenies` therefore makes both actual maps
etale. Each is smooth of relative dimension zero. Composition with the structure
map of relative dimension `g`, followed by the actual over-category equation,
gives relative dimension `g` on its source. Using the two maps proves both
directions. Here `AbelianScheme.HasRelativeDimension` is the existing smooth
relative-dimension predicate; no general rational-isogeny dimension theorem is
assumed.

## Actual Harris construction

`cmIntegralOrderModel` first uses the dual witness and polarization already in
`X`. `DualWitness.forall_finset_fibre_affine` derives an affine open containing
any finite subset of one fibre from the displayed generic geometric premise.
The existing `D.harrisIntegralOrderModel` then constructs an integral model for
`D.harrisRationalOrderAction C X.actionObj.abelianScheme X.actionObj.action`.
It uses the original normalized reflex map
`D.harrisTaylorReflexStructure C Z.obj.hom`, the actual positive Harris order
and its existing integral basis.

`cmIntegralOrderModelDualWitness` selects dual evaluation data for this actual
model abelian scheme from `Z.property.dualExists`. The selection concerns only
its dual presentation. It does not supply the integral model, its polarization,
or a representing scheme for the CM moduli presheaf.

`cmPolarizedOrderModel` applies the existing
`PolarizedAction.orderModel` construction. The resulting object carries the
rational extension of the actual integral action and the actual dual pullback
of the original polarization. That construction proves geometric polarization,
faithfulness and compatibility with the entire original auxiliary involution.
The characteristic-zero map used for the polarization argument is the original
`Z.obj.hom` to the CM field spectrum.

`cmPolarizedOrderModelIso` retains the exact equivariant rational isomorphism
coming from this model's actual forward homomorphism and its prescribed inverse
multiple. `cmPolarizedOrderModelRestriction` supplies the integral Harris order
action on this same polarized representative, with the original rational
restriction equation.

## Original normalized conditions and multiplier

`cmPolarizedOrderModel_condition_iff` preserves exactly the existing conjunction
`HarrisTaylorCMDeterminantDimensionCondition`, evaluated at the original CM
structural map. The determinant component is transported by
`harrisTaylorCMRationalLieDeterminantCondition_iso` using the underlying actual
rational isomorphism and its equivariance. The dimension component is the
preceding two-map relative-dimension argument. The determinant polynomial and
its normalization are unchanged.

`cmPolarizedOrderModelMultiplier` is the rational unit whose value is `N^2`,
where `N` is the same positive integer in this model's integral inverse data.
`cmPolarizedOrderModelMultiplier_pos` proves its positivity in the original
rational ordering. `cmPolarizedOrderModel_multiple` gives the exact existing
`PolarizedWeilLevel.Multiple` relation for the original action, the constructed
action, this unit and `cmPolarizedOrderModelIso`. It uses the ordered-pair
additivity supplied by `Z.property.pairAdditivity` and the existing exact
`PolarizedAction.orderModelMultiple` computation.

This unit constructs neither level orbits nor an integral representative of a
normalized class. It does not prove surjectivity of the integral class image,
scheme representability, smoothness, division-case projectivity or the main
`DivisionCMRepresentabilityStatement`. Those consumer conclusions remain
separate obligations. In particular, the full generic proper-family
fibre-ampleness theorem remains a premise of the constructions here.
