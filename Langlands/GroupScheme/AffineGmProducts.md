# Products and comparison of actual action interfaces

This internal construction compares the Library's categorical `SchemeAction`
with its actual-morphism, all-test-law `PointwiseSchemeAction`. Both conversions
retain the action morphism and every test-point action; their composites are the
identity. Fixedness agrees on every relative refinement. For a multiplicative
group action, the actual orbit morphisms and orbit-extension equations also agree.
The categorical conversion reuses `schemeActionOfPointLaws`.

The diagonal product action is the existing `PointwiseSchemeAction.prod` from
`ImageGenerationCommutator`. Both projections are equivariant. A point of the
product is fixed precisely when both projections are fixed on all refinements.
Its actual orbit has an affine-line extension precisely when both projected
orbits do: project an extension in one direction and pair two extensions in the
other. These assertions impose no affineness, smoothness or field assumption.

Over any commutative base ring, for two affine targets, the actual fixed scheme
of the diagonal product action is isomorphic over the base to the product of the
actual fixed schemes. The same assertion holds for attracting schemes. The
forward maps are induced by the two projections. Conversely, the product of the
two closed inclusions is respectively fixed or attracted, so all-test
representability gives an inverse. Cancellation against the closed inclusions
proves the inverse identities and verifies that the comparisons retain the
actual inclusions into the original product. All relative scheme tests and all
universes are retained.

These are internal consequences of the existing action laws, binary-product
universal property and actual all-test fixed/attracting representability. No
external literature assertion is transcribed. This module supplies neither orbit
closedness, reductive quotient affineness nor the dynamic quotient
properness theorem `DynamicQuotientProperStatement` that it serves.
