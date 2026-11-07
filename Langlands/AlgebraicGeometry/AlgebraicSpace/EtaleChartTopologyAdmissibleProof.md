# Proof of Conrad's Proposition 5.4 (corrected to locally separated spaces)

Author: Worker 105.

This module proves `EtaleChartTopologyAdmissibleStatement`: Proposition 5.4 of Brian
Conrad, *Weil and Grothendieck approaches to adelic points* (December 31, 2011), printed
pp.14–15 (source
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`), topological part,
corrected to locally separated spaces as explained in the Markdown of
`HenselianSpacePointTopologyStatement`.

- `etaleChartTopology_isAdmissible`: over a henselian valued field, the étale-chart
  topology satisfies the six clauses of `IsAdmissibleRationalPointTopology`. Each clause
  assumes that the spaces satisfy `IsLocallySeparatedLocallyFiniteType`, whose first
  component is `IsQuasiSeparatedLocallyFiniteType`.
  - functoriality: `continuous_ringPointsMap` (`EtaleChartTopologyFunctorial`);
  - schemes: `isHomeomorph_schemeRingPointsEquiv` (`EtaleChartTopologyFunctorial`);
  - fibre products: `isEmbedding_pullbackPoints` (`EtaleChartLocalSeparation`);
  - open immersions: `isOpenEmbedding_ringPointsMap` (`EtaleChartTopologyFunctorial`);
  - closed immersions: `isClosedEmbedding_ringPointsMap` (`EtaleChartTopologyFunctorial`);
  - étale morphisms: `isLocalHomeomorph_ringPointsMap` (`EtaleChartLocalSeparation`).
- `etaleChartTopology_separatedProperties`: the three separated-space properties of
  `SeparatedRationalPointTopologyProperties`: Hausdorff and locally compact from
  `EtaleChartSeparated`, totally disconnected from `EtaleChartTotallyDisconnected`.
- `etaleChartTopologyAdmissible : EtaleChartTopologyAdmissibleStatement`. Admissibility and
  the separated properties are as above. Uniqueness is
  `eq_etaleChartTopology_of_isAdmissible` (`EtaleChartTopologyUniqueness`).

The proof route follows Conrad's, with these changes. Open and closed immersions are
treated directly with charts. The étale and fibre product properties use the embedding of
rational points of chart overlaps into products, which holds because the space is locally
separated. Hausdorffness uses closed chart overlaps. Total disconnectedness over
non-locally-compact fields needs an argument that Conrad does not give: images of bounded
clopen balls of affine charts are clopen.
