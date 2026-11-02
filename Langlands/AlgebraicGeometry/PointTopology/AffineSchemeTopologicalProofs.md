# Topological proofs for actual affine scheme points

Author: Worker 105.

This proves `AffineSchemeTopologicalProperties`, the relative actual-scheme
Hausdorff and local-compactness assertions derived from Conrad, *Weil and
Grothendieck approaches to adelic points* (December 31, 2011),
Proposition 2.1, second paragraph and proof, printed page 2. Registered
source: `conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

The actual global-section point homeomorphism identifies actual relative
scheme points with algebra maps endowed with their evaluation topology.
The published Hausdorff instance for algebra-map points and the embedding
underlying this homeomorphism give Hausdorffness for arbitrary affine
schemes. Only Hausdorffness of the value algebra is needed.

For local compactness, the published instance
`affineCoordinate_finiteType` turns local finite type of the actual affine
structure morphism into finite type of its actual global-section algebra.
The published `affineLocalCompactness_proof` then gives local compactness
on the algebra-map side. The closed embedding underlying the same
homeomorphism transfers this property to the actual scheme point space.
This branch uses the separate topological-ring, Hausdorff and local
compactness hypotheses on S. The final theorem assembles both branches
exactly as in the target.

All rings and schemes share one arbitrary universe. There is no topology
on R, no finite-presentation requirement and no nonaffine conclusion.
