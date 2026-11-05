# Composition of actual closed-immersion cohomology maps

This internal development derives transitivity from the actual sections
composition laws, compatible-resolution formulas and acyclic-resolution
comparison theorem. All schemes and coefficient rings have an arbitrary
common universe. The sheaves are unrestricted scheme modules.

`compositePushforwardModuleMap` composes actual coefficient maps into two
successive pushforwards and the canonical pushforward composition map.
The construction itself does not require closed immersions.

For two closed immersions and commuting affine-base squares,
`closedImmersionCohomologyMap_pushforwardComp` compares the canonical
cohomology map of the pushforward composition isomorphism with two
successive canonical cohomology maps. The canonical scalar-restriction
composition map is retained. The composite square is supplied by the existing
`sectionsBaseChangeSquare_comp` from
[`SectionsBaseChangeComposition`](SectionsBaseChangeComposition.md).

`closedImmersionCohomologyMap_precomp` expresses compatibility with
precomposition of coefficient maps. Using this identity and naturality
in the target coefficient, `closedImmersionCohomologyMap_comp` proves
transitivity for arbitrary maps `M → h_*N` and `N → j_*P`. The composite
is exactly `compositePushforwardModuleMap`; its cohomology map followed
by scalar-restriction composition equals the first canonical cohomology
map followed by the restricted second map. This holds in every
nonnegative cohomological degree.

The proof uses an injective resolution on the last scheme. Exactness of
closed-immersion pushforward gives the two preceding resolutions. Their
source terms are canonically isomorphic to pushforwards of injectives,
so the published pushforward acyclicity and acyclic-resolution comparison
make the source comparison invertible. The compatible-resolution formulas
and sections cohomology composition law then prove the identity after
cancellation. No quasi-coherence, flatness or properness is assumed.

This is an internal formal consequence of the imported constructions,
not an additional geometric premise. Tensor and obstruction naturality
and the exact Picard-stack atlas theorem remain further obligations.
