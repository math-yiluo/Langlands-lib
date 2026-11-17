# Actual Weil presentation from an étale permutation atlas

This derived module completes the general permutation-atlas construction. Given
an arbitrary small étale permutation atlas for a group scheme over Spec R,
`permutationAtlasWeilPresentation` proves the unchanged
`PermutationAtlasWeilPresentationStatement` in every universe: there exists an
actual commutative R-algebra E which is finite, projective and étale, together
with an actual group-scheme isomorphism from the supplied group to
`WeilGm.groupScheme (CommRingCat.of R) E`. No affineness hypothesis on the group
scheme is supplied, and varying and empty chart coordinate types are allowed.

`finiteAffineWeilIso` first constructs the actual comparison for a finite affine
étale permutation atlas over an arbitrary affine scheme S. The multiplicative
coaction on the chart product coefficients has the actual invariant algebra.
Its finite, projective and étale properties and actual local coefficient
splittings were established in the imported modules. The resulting actual Weil
charts have exactly the same local all-test permutations as the original
charts. `matchingChartsIso` therefore glues the actual local comparisons and
their inverses to an actual global group-scheme isomorphism.

`HasEtalePermutationAtlas.exists_weilGroup` refines the given atlas to a finite
affine étale cover using compactness of the affine base. It retains the actual
charts and local permutations. The cover gives flatness and joint surjectivity,
so the invariant coefficient algebra and the preceding comparison apply. The
result is initially expressed over the global-section ring of S and pulled back
along the canonical affine isomorphism from S to its spectrum.

For S = Spec R, the canonical ring isomorphism from its global sections to R
induces exactly that affine scheme isomorphism. Base change of the coefficient
algebra to R gives the actual algebra R tensor E. Finiteness, projectivity and
étaleness are preserved by this base change. Composing the global comparison
with the published Weil base-change isomorphism proves the specified
arbitrary-ring presentation. This avoids identifying the two scalar structures
by an implicit transport.

The provenance is internal and derived from actual coefficient descent,
normalized chart restriction, Weil point models and étale-cover gluing. This
unit establishes the abstract permutation-atlas ingredient. It does not construct
the supplied-relative-Borel atlas and does not by itself prove the host
`RelativeBorelAdjointTorusWeilPresentationStatement`.
