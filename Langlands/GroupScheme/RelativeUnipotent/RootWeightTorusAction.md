# Actual torus actions on represented root-weight terms

This derived module constructs actions from actual ambient root maps, for an
arbitrary commutative base ring. Its input is a `RootHeightChart` C on a group U,
a monomorphic group homomorphism j from U into G, an actual split-torus homomorphism
t into G, and a family of torus-equivariant root parametrizations whose ambient
composites are the ordered root maps of C. No reductivity or strictly positive
secondary-weight assumption is used in this module.

`RootHeightChart.torusAction` is the actual conjugation action of that torus on U.
The construction proves stability of the range of j: write any point in the
original ordered root coordinates and use torus equivariance to scale each
coordinate by its root character. Represented-subgroup factorization then gives
the action morphism and its group-action laws. `torusAction_comp` records its exact
ambient conjugation equation, and `coordinates_torusAction` identifies the action
in the original chart as the stated diagonal scaling.

For every `RootWeightData` W on C, including secondary weights equal to zero,
`RootWeightData.torusAction` constructs the actual torus action on every
represented term W.groupScheme d. The coordinate-vanishing criterion for W proves
stability because scaling a zero coordinate leaves it zero. The inclusion is
equivariant, and `range_inclusion_isNormalizedBy_torus` proves that its actual
ambient range is normalized by the full ambient torus range. The final coordinate
identity specifies its exact root characters.

All identities and stability statements hold on every scheme test, including
nonreduced tests. This is normalization by the supplied torus. Normalization by
the entire parabolic, intrinsic cyclic-cutoff identification, and compatibility
when changing maximal tori remain separate steps of the finite vector-bundle
filtrations of supplied relative radicals.

The ambient ordered-product identity reuses
`LocalSplitCell.orderedProduct_chart_comp` from `SplitWeightDynamicComparison`.
