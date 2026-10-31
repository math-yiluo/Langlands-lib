# Actual subspaces covered locally by contained original charts

This module constructs the supplied affinoid atlas on an arbitrary subspace
whose contained original charts give finite relative neighborhoods. It retains
all those charts, their original positive-polyradius affinoid algebras, and
every original bounded restriction. No directedness or ambient Hausdorffness
is required.

The coefficient field `K : Type u` is complete, normed and nonarchimedean.
The ambient space and original chart indices have independent universes `v`
and `w`. Reducedness is not assumed.

`IndexedAffinoidAtlas.IsOriginalChartDomain S` is the concrete topological
condition that the original chart domains contained in `S`, regarded as subsets
of `S` with its induced topology, form a quasinet. Thus at each point there is
a finite family of contained original chart domains, each containing the
point, whose union is a relative neighborhood. This condition supplies no
algebras, bounded maps, intersection axiom, or output analytic atlas.
Every original chart domain satisfies it, as does the empty subspace.

`SubspaceChart S` consists of exactly the original indices whose chart range
lies in `S`. `subspaceChart` restricts the codomain of the original spectrum
embedding. Its range is the preimage of the original range under subspace
inclusion. The two containment lemmas compare containment of these ranges
with original chart containment.

`isNet_subspaceChartFamily` derives the entire net axiom from the existing
ambient net and the finite relative neighborhood condition. It uses the
published `IsNet.restrict`: the original pairwise intersection quasinets
transport through the actual nested-subspace homeomorphism. Local
Hausdorffness passes to every subspace by intersecting an ambient Hausdorff
neighborhood with that subspace and using the induced embedding into the
Hausdorff neighborhood.

`subspaceAtlas` now constructs the atlas. Each algebra and every bounded
restriction is literally the original one at the underlying index. The
original domain universal property proves the same full factorization for
all presented affinoid tests, including nonstrict and empty tests; applying
subspace inclusion to a chart equality transfers the image condition.
The restriction identities and composition are inherited. The original
single-chart atlas is recovered by `subspaceAtlas_chart`.

`AffinoidAtlasPresentation.subspacePresentation` bundles this actual subspace
and atlas. `subspaceInclusion` and `subspaceMap` construct the chosen inclusion
arrows, using original chart indices and bounded identity homomorphisms.
Their identity, nested composition and ambient inclusion equations are
equalities of complete chosen arrows.

`StrongHom.restrictSubspace` restricts a full strong morphism only on the
source. The target atlas is retained. The exact admissibility equivalence
identifies every pullback with the original bounded homomorphism on the
underlying source index; the original two-variable naturality equation
proves the new one. `subspaceStrongInclusion` is source restriction of the
full identity, so it retains the original bounded restriction for every
admissible source and target pair. These constructions do not require
directed charts or general strong composition.

The construction is derived from Berkovich, *Étale cohomology for
non-Archimedean analytic spaces* (1993), registered as
`berkovich-1993-etale-cohomology`: section 1.1, printed pp.13–14 / PDF
pp.10–11, defines quasinets, induced topologies and contained-member
families; Definition 1.2.3 and Remark 1.2.4(i), printed p.16 / PDF p.13,
give the atlas and bounded restriction conventions; Definition 1.2.7,
printed p.18 / PDF p.15, gives full strong morphisms. The arbitrary-subspace
constructor and its chosen and full inclusion maps here are internal
consequences of those conventions and the published restriction lemmas.

This covers subspaces locally covered by contained original charts. It does
not construct additional rational or affinoid domains, assert that every open
subset satisfies the condition for a fixed coarse atlas, establish the
saturated extension of Proposition 1.2.6, or construct an analytic site.
