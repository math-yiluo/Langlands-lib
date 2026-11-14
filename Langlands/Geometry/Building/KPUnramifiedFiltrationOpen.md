# Openness for supplied building filtrations over the maximal unramified field

These internal supporting results use the actual maximal unramified field with
`fixedFieldTopology F` and the canonical rational-point topologies.
Integer normalization preserves the character valuation kernel by
`MaximalUnramified.valuation_isEquiv`. The supplied centralizer is connected
reductive by `IsSplitTorus.isConnectedReductive_centralizer_of_dynamic` and
`dynamicCentralizerReductive`, so its kernel is open by
`isOpen_characterValuationKernel_of_isConnectedReductive`.
`MaximalUnramified.exists_order_ne_zero` supplies nontriviality, so
`IntegerValuationBuildingData.isOpen_filtration` proves relative openness of
every root filtration at every real depth.
`rootFiltrationOpenSubgroup` bundles exactly
`(B.filtration x α r).subgroupOf (B.rootGroup α)` as an open subgroup, with
no character-kernel or nontriviality premise remaining.

`isOpen_moyPrasad_of_isOpen_torus` applies
`RelativeRoot.topologicalRootCentralizerGeneration` to the actual root
filtrations and centralizer torus filtration. The published
`moyPrasad_eq_sup_iSup` identifies their generated subgroup with the supplied
Moy–Prasad group. This lemma retains openness of the torus term as a premise;
it does not by itself prove the final comparison-openness statement.
