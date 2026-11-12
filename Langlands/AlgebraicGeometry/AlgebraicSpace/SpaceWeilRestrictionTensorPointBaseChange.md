# Cartesian base change on tensor Weil points

This internal supporting unit for Conrad's Proposition 5.14 compares the
published cartesian space isomorphism with the original-coefficient tensor
point equivalence. It retains the algebraicity hypothesis and both original
coefficient maps. It proves no representability or adelic endpoint assertion.

The base-point test map has first projection the original lower coefficient
map, as follows from tensor multiplication and functoriality of spectra.
The canonical base-point equivalence is evaluation on this test isomorphism,
by contravariant presheaf composition.
The composite test map for the cartesian comparison is then equal to
the tensor test map followed by restriction of scalars on the original test.
The proof uses the two projections of the actual scheme pullback.
Applying the original space presheaf to this equality proves the stated
point diagram, with the local Weil base-point equivalence and the canonical
base-change point identifications on the other three sides.

`ringWeilRestrictionTensorBaseChangePointsEquiv` packages the resulting
equivalence from rational points of the base-changed Weil space to the
original space's `D`-valued points. Its definition first removes the lower
base change and then applies the tensor point equivalence.
`ringWeilRestrictionTensorBaseChangePointsEquiv_apply` identifies this with
the cartesian space isomorphism followed by the local Weil base-point and
upper base-change identifications.

The provenance is internal: these identities follow from the published
tensor-spectrum and cartesian base-change constructions, the universal
property of scheme pullbacks, and evaluation of the original space presheaf.
