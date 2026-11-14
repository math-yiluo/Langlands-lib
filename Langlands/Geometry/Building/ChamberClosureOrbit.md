# Chambers through a point form a nonempty full-fixer orbit

`IntegerValuationChamberClosureOrbitStatement` asserts existence and full-fixer
transitivity of `HasChamberClosurePresentation`, for every supplied
`IntegerValuationBuildingData` over any field and any integer-valued valuation.
There is no local-field or order-one-unit hypothesis. The statement is proved by
`integerValuationChamberClosureOrbit` at arbitrary universe `u`.

This is an internal consequence of the existing affine-root and quotient
constructions. It preserves the exact translated generic-facet and closure
witnesses needed by `UnramifiedTwistedChamberThroughFixedPointStatement`.
It introduces no new external source assertion.

## Implemented proof

`exists_chamberClosurePresentation` writes the given building point as
`g • apartmentMap x`. The published locally finite reflection arrangement
theorem, using the established opposite-factor-pair existence, supplies a
regular apartment point whose facet closure contains `x`. Its translated
facet has the required presentation.

`exists_normalizer_fixing_facet` applies the existing affine Weyl chamber
transport at a common closure point. The containment of the affine Weyl group
in the actual normalizer action lifts this transport to an actual normalizer
element. Root preservation identifies its image with the second regular
facet, and it fixes the common point.

For `exists_fixer_smul_chamber_eq`, write the two presentations as
`g₀ facet(x₀)` and `g₁ facet(x₁)`, with closure points `a₀` and `a₁` both mapping
to `y`. Equality in the actual apartment quotient gives a normalizer element
`n` with `n a₁ = a₀`. The normalizer preserves regularity and facet closure.
The preceding transport supplies `m` fixing `a₀` and taking `facet(x₀)` to
`facet(n x₁)`. The actual group element

`g₁ n⁻¹ m g₀⁻¹`

then fixes `y` and maps the first chamber to the second. Both assertions are
checked directly by the group-action identities and normalizer covariance
of `apartmentMap`. The unused sharp-fixer clause of the quotient equality is
unnecessary for this full-fixer conclusion.

## Scope

The acting group here is the full point fixer. This result does not prove
transitivity for a specified smaller parahoric, construct a reductive quotient,
prove a reduction map surjective, identify its kernel, or establish compatibility
with finite-field Frobenius. These remain inputs to the separate quotient
construction. The result also does not assert Galois or twisted stability of the
chosen chamber.
