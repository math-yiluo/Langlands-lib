# Finite real spaces of actual split tori

Author: Worker 1319.

This internal unit transports the published actual character and cocharacter lattices along an isomorphism of commutative group schemes, then extends those identifications to the already published real spaces `RealTorusSpace.V` and `Vstar`. `cocharacterRealCongr` is postcomposition on pure cocharacter tensors. `characterRealCongr` is inverse precomposition on pure character tensors. `pair_congr` proves that these maps preserve the real pairing, by tensor induction and the published integral identity `latticePairing_congr`.

For every actual split torus over any field, `IsSplitTorus.finite_realCocharacterSpace` and `finite_realCharacterSpace` prove finite dimensionality of its full real spaces. `finrank_realCocharacterSpace` and `finrank_realCharacterSpace` identify both dimensions with `splitTorusRank`, the rational dimension of the full character lattice.

Each proof extracts the finite split-torus presentation from `IsSplitTorus`, turns its group-scheme isomorphism into the corresponding isomorphism of commutative group schemes, and uses the published split coordinate equivalences. The dimension proofs also transport the full rational character space to the same finite function space over `ℚ`. Both function spaces have dimension the cardinality of the index type. No nonempty index set is required, so rank zero is included.

The provenance is internal finite lattice algebra based on `Torus.LatticeGalois`, `SplitRealTorusSpace`, `LinearAlgebra.RationalSpan` and Mathlib's dimension transport. This unit supplies the first four conclusions of the central-direction target whenever the supplied torus is split. It does not prove the geometric split-component embedding or the root-annihilator comparison.
