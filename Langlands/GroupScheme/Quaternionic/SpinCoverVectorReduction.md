# Reduction of aligned spin vector weights to supplied representation inputs

`TitsIndexData.HasSpinVectorWeights` is the exact existential conclusion of
`SpinCoverVectorWeightsStatement` for the supplied actual index, numbering,
division algebra, form and spin cover. It records the numbered simple-root
formulas, existence of every signed pair root, and the signed-weight count as
the degree times the original division-algebra weight-space dimension.

The generic `weight_card_of_descended_eigenbasis` combines the two-step
character descent and restriction identity with the previously proved
`weight_card_of_characterBasis`. Its supplied eigenbasis is an inverse-right
row eigenbasis over every coefficient algebra. The cocharacter square is an
explicit hypothesis of this generic calculation.

`spinCoverVectorWeights_of_basis` specializes that calculation to the actual
Tits-index torus map. It uses `spinVectorCocharacter_square` for the original
spin cover and supplied Morita comparison. The supplied character family's
numbered root equations and the resulting multiplicities give
`HasSpinVectorWeights`.

`spinCoverVectorWeights_of_comparison` assumes
`OrthogonalMatrix.NumberedCoverVectorStatement` and a supplied Morita comparison
over an algebraic extension of the separable closure. It transports the
alignment at the vertices labelled zero along the actual iterated cover,
applies `numberedVectorBasis_baseChange_of_statement`, then applies the basis
calculation. The characters descend to the actual pinning torus over the
separable closure; the dimension formula concerns the original action on the
original division-algebra module.

This is a derived conditional reduction in arbitrary universe `u`. There is no
restriction on field characteristic or cardinality. It proves neither the
numbered-cover input nor existence of a Morita comparison. It does not yet
supply an unconditional theorem of type `SpinCoverVectorWeightsStatement`.
Its provenance is the explicit composition of the existing actual pinning,
character-descent, spin-cover comparison and weight-multiplicity constructions;
there is no new literature assertion.
