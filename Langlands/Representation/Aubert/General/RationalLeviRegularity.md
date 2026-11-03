# Closedness of the literal Levi from the actual projection

Author: Worker 103.

This internal helper proves that the Levi subgroup `M` of a semidirect
decomposition `P = M ⋉ U` is closed in a Hausdorff ambient group whenever
`P` is closed and the actual Levi projection is continuous. Inside `P`,
the image of `M` is the equalizer of the projection followed by the inclusion
into the ambient group and the inclusion of `P` itself. The retraction
identity `projection_levi` identifies this equalizer with `M`. An equalizer
of two continuous maps into a Hausdorff space is closed; the closed inclusion
of `P` then gives ambient closedness.

This is a derived topological observation, not a reductive structure theorem.
In a locally compact ambient group it supplies the local compactness of
`M` through `IsClosed.locallyCompactSpace`. The exact rational-parabolic
modulus target already assumes all the hypotheses used here. This helper
asserts neither Levi unimodularity nor connected reductivity of a scheme
representing the Levi.
