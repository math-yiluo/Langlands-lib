# Proof of the multiplicative spectrum foundation target

Author: Worker 36.

`Langlands.Analytic.spectrumProperties` proves the entire proposition
`Langlands.Analytic.SpectrumPropertiesStatement`. Its auxiliary arguments
are implemented in `Spectrum.Properties` and
`Spectrum.LaurentNeighborhoods`; their paired Markdown gives the detailed
source correspondence and proofs.

The original source context is Berkovich's *Non-archimedean analytic spaces*
(Trieste lectures, 2009), printed/PDF pp.4 and 9-10, registered as
`berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
The [author's PDF](https://www.wisdom.weizmann.ac.il/~vova/Trieste_2009.pdf)
is the retained source. The implemented proof is direct and proves only
the precise scope of the proposition.

Evaluate each seminorm as a real function on the underlying ring.
Extensionality proves this map injective. The topology is the induced
evaluation topology, so it is an embedding into a Hausdorff space.
Its image is the set of functions satisfying the seminorm identities,
inequalities and norm bound. Each condition defines a closed set by
continuity of the corresponding coordinates and of real arithmetic.
The image lies in the product of the compact intervals
\([0,\lVert a\rVert]\), proving compactness. Its closedness and embedding
give the claimed closed embedding.

The kernel is proper because evaluation at one is one. Multiplicativity
and the real zero-product property prove the prime condition. For a
nonzero field element \(a\), apply norm domination to \(a^{-1}\) and
multiply using \(x(a)x(a^{-1})=1\). This gives the reverse norm inequality.
Zero is handled separately. Pullback along the bounded scalar map then
gives scalar normalization for an algebra.

Laurent inequalities are intersections of closed evaluation sublevel and
superlevel sets, hence closed and compact in the compact spectrum.
Their pullback formula follows from the actual composite evaluation.
For finite compact neighborhoods, the proof in `LaurentNeighborhoods`
shrinks a finite product neighborhood to positive-radius coordinate
balls. Upper thresholds are \(x(a)+\epsilon_a\); lower thresholds
\(x(a)-\epsilon_a\) are kept only when positive. Nonnegativity replaces
the omitted lower inequalities. Strict inequalities at the point prove
interior membership, and the coordinate bounds prove containment.

The closing theorem assembles these established results with no additional
mathematical premises. It assumes neither spectrum nonemptiness, an
analytic-domain factorization theorem, a structure sheaf nor a cohomology
output. Native compilation of this draft is not independent proof
acceptance or Library publication.
