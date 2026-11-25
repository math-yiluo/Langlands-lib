# Algebra coactions from functorial chart transitions

This module uses the chart-transition interface `ChartAlgebraDescent.Datum` of `ChartAlgebraTransport`.

For arbitrary commutative rings `A → B → C`, this internal module converts a
`ChartAlgebraDescent.Datum A B C` into an actual
`FaithfullyFlatAlgebraDescent.Coaction`. Formation of this coaction requires no
flatness, étaleness, finiteness or nonzero-ring hypothesis. Its target is the
actual algebra `B tensor_A C`, with the displayed ring-map scalar structures.

First the module retains compatible point transport as an underlying ring
homomorphism, together with its compatibility, identity, cocycle and naturality
laws. This form allows comparison of points with equal chart maps without
confusing their algebra structures. For `U = B tensor_A C`, the left chart is
`b ↦ b tensor 1`; the right chart is `b ↦ 1 tensor F(b)`. Transporting the point
`c ↦ 1 tensor c` from the right chart to the left gives `coactionMap`.

Multiplication `U → C`, `b tensor c ↦ F(b)c`, identifies the two charts.
Transport naturality and the identity law therefore prove the counit identity.
In `B tensor_A (B tensor_A C)`, naturality compares applying the coaction twice
with transporting through the intermediate chart. The transport cocycle
identifies this with direct transport, giving coassociativity. The proof
retains the actual ring homomorphisms in this comparison.

The final constructor packages the map and these two proved identities into
the existing module-descent comonad, after normalizing scalar actions to the
input ring maps. The displayed comonad maps agree with the actual tensor
algebra maps by induction on pure tensors. `coaction_map_apply` records the
resulting point formula with precisely those scalar structures.

This is an internally derived conversion from tensor adjunction and the three
chart-transition laws. It supplies the coaction needed to apply the existing
invariant-algebra effectivity theorem. This module does not prove the
full finite étale chart descent statement or its universal invariant recovery;
the statement is proved as `finiteEtaleChartDescent` in
`FiniteEtaleChartDescentProof`, which uses `ChartAlgebraDescent`.
