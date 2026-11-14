# Incident facets in the actual derivative arrangement

This module is an internal geometric construction from the existing affine
root, facet, localization and transport definitions. The vector space `V`
and affine torsor `A` have independent universes `u` and `v`. The initial
constructions assume only a real module, its affine torsor and an arbitrary
set `Ψ` of affine functionals.

`linearRootArrangement Φ` is the image of the given linear forms under
`LinearMap.toAffineMap`. In particular, no choice of an abstract root system
or a replacement collection of forms enters the comparison.
`vanishingRootDerivativeEquiv Ψ x` is the derivative map on the roots through
`x`, with codomain their actual derivative image. Its injectivity is the
published `linear_injOn_vanishingRoots`; surjectivity is image membership.

Translation by `y ↦ y -ᵥ x` turns an affine root vanishing at `x` into its
linear derivative. `affineFunctionalTransport_vsub_eq_linear` proves this
by the affine-map translation formula. Consequently
`transportedRoots_vanishing_eq_linearRootArrangement` identifies the entire
translated vanishing-root arrangement with the actual derivative
arrangement. The existing full-facet transport equivalence yields
`vanishingFacetDerivativeEquiv`; the existing face-transport theorem upgrades
it to `vanishingFacetDerivativeOrderIso`. Both orders are explicitly the
original `IsFaceOf` relations of their arrangements.

`incidentFacetDerivative F` first takes the unique localized facet containing
the incident full facet `F` and then translates it. It contains every point
`y -ᵥ x` for `y ∈ F`. Its original face relation preserves and reflects the
original incidence of incident facets, without any finiteness assumption.
If the roots separating `x` and each `y` form a finite set,
`incidentFacetDerivativeOrderIso` composes the existing localization order
isomorphism with the derivative order isomorphism. It therefore reaches
every facet of the derivative arrangement. The corrected affine-root-system
axioms with rank zero supply the finite-separation premise.

`nonnegativeLinearRoots Φ C` consists of the actual forms in `Φ` nonnegative
on all of `C`. The affine-map difference formula identifies it, on a
translated subset, with the derivative image of the original vanishing-root
support. Localization preserves that support, so
`nonnegativeLinearRoots_incidentFacetDerivative` gives the exact formula for
the derivative facet of an incident full facet. When `Ψ` is stable under
negation, reverse inclusion of these actual linear supports is equivalent
to original facet incidence. This follows from support detection before
translation and injectivity of the derivative on roots through `x`.

All proofs are elementary consequences of the imported Library definitions
and the stated existing geometric APIs. This module makes no assertion
about realization by integral cocharacters, special-fibre root data,
parabolic subgroup functors, or images of integral models. Those remain
separate inputs to the parabolic-order theorem.
