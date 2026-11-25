# Testing scalar section derivatives at infinite compact identity

`normalizedCoefficientMap` is the linear map from a smooth compact-finite scalar section to its normalized Levi coefficient at a fixed compact point. Evaluating a compact translate at infinite compact identity tests the original section at the translated compact argument, with the finite compact component held fixed.

The actual section derivative obeys the adjoint covariance of the enveloping action. `intertwines_sectionDifferential_of_identity` uses this covariance and the corresponding source covariance to extend a differential comparison at infinite compact identity to all compact evaluations. The scalar compact picture then gives equality of sections. The comparison applies to all source vectors and each finite compact argument.

This is internal to the route toward `CuspidalIsobaricAutomorphyStatement` (automorphy of isobaric sums of cuspidal representations at every place). Getz and Hahn (2024), §10.1, pp. 270–271 (PDF 282–283), give the normalized scalar compact picture. The Lean proof uses that picture's evaluation equivalence and the Library's compact adjoint law on the actual scalar sections.
