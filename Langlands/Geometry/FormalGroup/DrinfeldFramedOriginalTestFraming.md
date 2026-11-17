# Actual original normalized and refined framings on restricted tests

This internal unit identifies the original normalized framing appearing in the
constructed base-change square with direct scalar transport of the same actual
old framing. It also constructs the corresponding transported framing on any
specified original further refinement. It makes no new literature assertion.

`originalChartReAlgebra_eq_transport` eliminates the equality between induced
and supplied scalar structures and identifies the original-chart construction
with the existing global actual quasi-isogeny scalar transport on the same
test ring. Its proof retains the exact old chart map at reflexivity.

`normalizedOriginalFramingOnRestrictedTest` evaluates the given actual original
normalized framing on the test restricted along the induced Nilp quotient map,
then transports its scalars using the proved test scalar equality.
`refinedOriginalFramingOnRestrictedTest` does the same for a supplied original
further cover and chart. Both maps retain their actual rational inverses.

`baseChangeOriginalChartFraming_eq_transport` identifies the map in the prior
base-change normalization square with this direct transported original
framing on its retained selected original chart. It uses the exact
original-chart transport equation and preservation of composition, inversion
and rationalization under global scalar transport. No additional framing or
chart is chosen, and equality of point evaluations is not used.

The parameters retain the local field, finite-dimensional central division
algebra, embedded field, coefficient and residue fields, fixed height-certified
frame and Nilp objects in universes `{v,u}`. Each given original chart generator
must be invertible on the restricted test. Covers may be infinite and scalar
maps may merge generators. New-refinement transport and preservation of
original framed comparison squares remain further constructions.
