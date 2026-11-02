# Closed-immersion properties of actual scheme point spaces

This unit states that actual closed immersions of arbitrary relative schemes
induce embeddings on actual point spaces with the explicit affine-chart final
topologies. Hausdorffness of the value ring is required separately for closedness
of the image.

## Source and derived formulation

Brian Conrad, *Weil and Grothendieck approaches to adelic points* (December 31,
2011), Proposition 3.1 and its gluing proof, printed page 4, includes the
closed-immersion embedding assertion for locally finite type schemes over a
local topological ring with open units and continuous inversion. Proposition
2.1 and its proof, printed page 2, establish the affine embedding assertion and
its closed-image refinement for Hausdorff value rings by coordinate equations.
The registered source is `conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

This target is the derived relative and arbitrary-scheme extension of that
portion of the argument. The affine coordinate embedding and closed-image
arguments use every kernel equation and do not require finite generation.
A closed immersion has affine preimage over every affine target chart; its
restricted point map is the affine comparison. The local-ring/open-unit
hypotheses give open chart embeddings and cover the point spaces, so the
embedding and closed-image assertions can be tested in these charts.
Only continuous multiplication is needed for this gluing part. This explains
the absence of finite-type, finite-presentation or full topological-ring
premises in this isolated derived target.

## Exact target and hypotheses

`Langlands.AlgebraicGeometry.PointTopology.SchemePointClosedImmersionProperties`
uses commutative rings `R` and `S` in a common arbitrary universe,
`Algebra R S`, and a topology only on `S`. Its common hypotheses are
`IsLocalRing S`, `ContinuousMul S` and `IsOpenUnits S`. The last is the
separate open-subspace condition on units with their existing value-and-inverse
topology; it is not inferred from localness.

It quantifies over every actual `X` and `Y` in `Over (Spec R)` and every actual
relative morphism `f : X ⟶ Y` whose underlying scheme morphism is a closed
immersion. Both point carriers are the existing `RingPoint`, and both topologies
are explicitly `schemePointTopology`. The map in the conclusion is actual
postcomposition `p ↦ p ≫ f`.

The first conclusion is `IsEmbedding` without a separation hypothesis on the
value ring. The second adds `T2Space S` and concludes `IsClosedEmbedding` for
the same actual map and point topologies. Neither conclusion assumes separation
of the schemes, quasi-compactness or locally finite type. The statement says
nothing about pointwise complements of closed and open subschemes covering the
point set; Conrad Remark 3.3 warns that they need not.

This contribution supplies the target and proves neither conclusion. It does
not assert the separate product, uniqueness, Hausdorff or locally compact
conclusions of Proposition 3.1, or any adelic/nonaffine comparison from the
later sections.
