# Original coefficients on tensor Weil restriction points

This internal supporting construction for Conrad's Proposition 5.14
uses the published tensor cartesian comparison and actual test spectra.
It retains the algebraicity hypothesis for the original Weil sheaf.
It makes no representability or adelic-topology existence assertion.

`weilRestrictionTensorCoefficientEquiv` regards the given equivalence
`C ⊗[R] B ≃ₐ[C] D` as an equivalence of `B`-algebras in the opposite
tensor order. The original coefficient identity on `1 ⊗ b` proves its
`B`-linearity. `ringWeilRestrictionTensorPointsEquiv` composes the
published Weil point equivalence with this change of coefficients.
Its application formula is pullback along
`weilRestrictionTensorPointTestMap`. The two projection formulas retain
the original maps from `C` and from `B`.

For a product coefficient algebra, the component map
`completedTensorSpaceWeilRestrictionPointMap` evaluates the original
space on the published `completedTensorWeilRestrictionFactorTestMap`.
The equality theorem identifies it exactly with the tensor point
equivalence followed by the original product projection.

The naturality theorem states the commuting coefficient diagram when
`C → C'` and `D i → D' i` preserve both original scalar maps. Its proof
applies the original space presheaf to the published commuting square
of test spectra. This applies in particular to integral-to-field maps
when the corresponding coefficient compatibility has been supplied.
