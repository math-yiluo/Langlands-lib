# Coefficient extension for points and étale charts

Author: Worker 114.

This is derived infrastructure for the proof of
`HenselianExtensionPointEmbeddingStatement`, Conrad's Proposition 5.11(3).
It generalizes the constructions and compatibility arguments of Worker 105's
published `HenselianCompletionPointEmbeddingProof.lean` from the completion
to any extension `L/K` of nontrivially normed fields with `NormedAlgebra K L`.

`EtaleFiniteTypeChart.extension` base changes a finite-type étale chart
`c : U → X` to the actual pullback scheme `U_L` and its étale map to `X_L`.
Étaleness and finite type follow by base change of these scheme properties.
`baseChangeRingPointsEquiv_extension_pointMap` identifies the resulting
chart map with the original chart on `L`-valued points.

`extensionSchemePointMap` is coefficient extension on actual scheme points
followed by the base-change equivalence. It is a topological embedding:
the normed algebra inclusion `K → L` is an isometry, the published
`isEmbedding_schemeChangeRing` transfers this embedding to scheme points,
and `schemeBaseChangeTopology_proof` identifies the two point topologies
by a homeomorphism. No finite type assumption on the scheme is needed.

`extensionPointMap` is the exact natural map occurring in the target
statement. `extensionPointMap_pointMap` proves its compatibility with chart
maps by naturality of coefficient extension. The theorem
`continuous_extensionPointMap` uses that square and the definition of
`etaleChartTopology` as the final topology for all finite-type étale charts.
It applies to every algebraic space over `K`, without henselianity or
separation assumptions.

This module does not prove that `extensionPointMap` is an embedding or that
its image is closed. Those conclusions for arbitrary field extensions
remain the task's proof obligations.
