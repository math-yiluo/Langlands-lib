# Ground field extension preserves strong quasi-isomorphisms

The theorem
`Langlands.Analytic.AffinoidAtlasPresentation.GroundFieldExtension.groundFieldExtensionQuasiIso`
proves the unchanged published proposition
`Langlands.Analytic.AffinoidAtlasPresentation.GroundFieldExtension.GroundFieldExtensionQuasiIsoStatement.{u, v, w, u'}`.
The four universes are independent. The hypotheses are exactly those of the
target: `K` and `L` are complete ultrametric normed fields with
`NormedAlgebra K L`, and `f` is a compatible strong map between indexed affinoid
atlas presentations over `K` with `f.toStrongHom.IsQuasiIso`. No saturation,
ambient Hausdorffness, nontrivial valuation or finite degree is used. The proof
uses the standard axioms only (`propext`, `Classical.choice`, `Quot.sound`) and
sets `maxHeartbeats 1000000`.

Write `g` for the actual extended strong map `(compatibleMap K L f).toStrongHom`,
and `pA`, `pB` for the projections
`IndexedAffinoidAtlas.GroundFieldExtension.projection K L A.atlas` and
`... B.atlas` of the extended spaces to the original ones. Unqualified names
below are in the namespaces opened by the Lean file
(`AffinoidAtlasPresentation.GroundFieldExtension`,
`IndexedAffinoidAtlas.GroundFieldExtension`,
`PresentedAffinoidAlgebra.GroundFieldExtension`, `AtlasTopology`).

## Representation at every admissible pair

An admissible pair `(i, j)` of `g` is admissible for `f`, by `admissible_iff`
of `GroundFieldExtensionMaps`. The bounded pullback of `g` at that pair is, by
definition of the extended strong map, `map K L` of the original pullback,
which represents the original image locus `f.toStrongHom.chartImageLocus i j`
by the second clause of the hypothesis. The published affinoid-domain
preservation theorem `domainPreservation` then shows that the extended pullback
represents the preimage of that locus under `spectrumProjection K L`. This is
`hrep`. Since a representing map represents the range of its spectrum map
(`represents_range`), and that range is `g.chartImageLocus i j`
(`StrongHom.range_pullback`), the extended pullback represents the image locus
of `g`: the second clause of `IsQuasiIso` for `g`.

## Images of charts and the embedding property

`himage` says that the image under `g` of the extended source chart `i` is the
`pB`-preimage of the original image `f '' range (chart i)`. One inclusion is
the projection naturality `projection_pointMap` together with the chart-range
formula `range_chart` (`range (chart i)` of the extended atlas is the
`pA`-preimage of the original chart range). For the other, choose an original
target chart `j` with `f '' range (chart i) ⊆ range (chart j)`; it is
admissible for `g` by `admissible_iff`. A point of the preimage lies in the
extended target chart `j`, so it is `chart j t`; `t` lies in the represented
locus, which is the range of the spectrum map of the extended pullback, and
`chart_comm` lifts it to a point of the extended source chart `i`.

`hemb` shows that `g` composed with each extended source chart is a topological
embedding. Choose an admissible target `j`. The spectrum map of the
representing extended pullback is injective
(`comap_injective_of_represents`) and continuous from a compact space to a
Hausdorff spectrum, hence a closed embedding. Composing with the target chart
embedding `isEmbedding_chart` gives the claim, through the chart equation
`chart_comm`.

## Bijectivity and continuity of the inverse

Injectivity: if `g x = g y`, then `pA x = pA y` by naturality and injectivity
of the original homeomorphism. Choose an extended chart `i` containing `x`
(`exists_chart`); by `range_chart` the point `y` lies in it as well, and the
embedding `hemb i` gives `x = y`.

Surjectivity uses the family `τ` of `pB`-preimages of the images, under the
original homeomorphism `f.baseMap`, of the original source chart ranges. It is a
quasinet (`AtlasTopology.IsQuasinet`): the original source chart family is a
net, in particular a quasinet; its image under a homeomorphism is a quasinet
(`IsQuasinet.imageFamily`); and the family of preimages of a quasinet along the
continuous projection `pB` is a quasinet (`IsQuasinet.preimage_image`). By
`himage`, every member of `τ` is the image under `g` of an extended source
chart, and `τ` covers the target (`IsQuasinet.covers`), so `g` is surjective.

The inverse of the resulting bijection is continuous on each member of `τ`,
because there it agrees with the extended source chart composed with the
inverse of the embedding `hemb i`. The quasinet continuity criterion
`IsQuasinet.continuous` then makes it continuous globally. Hence the extended
base map is a homeomorphism (`isHomeomorph_iff_exists_inverse`), the first
clause of `IsQuasiIso`.

## Provenance and scope

The proof is the Library's own argument; the statement's provenance
(Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993),
Definition 1.2.9 and §1.4, registered `berkovich-1993-etale-cohomology`) is
recorded in the statement's Markdown.

This proves preservation of full strong quasi-isomorphisms by the actual
ground field extension of compatible strong maps. The resulting functor on the
localized categories, transitivity in field towers, fibre products and the
comparison with analytification are not stated or proved here.
