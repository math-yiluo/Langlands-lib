# Convex relative-root subsets and their finite conic hull

This module proves the published proposition
`Langlands.GroupScheme.ConvexRootSubsetHullStatement.{u}` by the theorem
`Langlands.GroupScheme.convexRootSubsetHull`. The setting is unchanged: an arbitrary
field, a connected reductive group scheme, a maximal split torus and either the full
relative-root set or its indivisible subset.

The proposition reformulates the definition of convexity in Renard,
*Représentations des groupes réductifs p-adiques*, French edition of 9 July 2026,
V.4.2, printed page 118 (PDF page 124). The source calls a root subset convex when
it is the intersection of the ambient roots with a closed convex cone. The precise
Library conventions and the two ambient root sets are documented in
`ClosedRootSubsetStatements.md`. This proof does not assert the other statements
in that file.

For the forward implication, write the subset as the intersection with a closed
cone `C`. Its generators belong to `C`, so minimality of `PointedCone.hull` puts
the entire hull inside `C`. Any ambient root in the hull therefore belongs to the
original subset.

For the reverse implication, use the conic hull itself as the witnessing cone.
The subset condition and the assumed hull saturation give equality with the
intersection of the ambient roots. It remains to check closedness. The published
`IsSplitTorus.finite_relativeRoots` proves root finiteness directly from the Lie
weight decomposition, using splitness and the affine locally finite type
hypotheses. Affineness and smoothness come from connected reductivity; smoothness
supplies local finite type. The indivisible roots form a subset of the full root
set. Hence the character subset and its image under `χ ↦ 1 ⊗ χ` are finite.

The internal helper `Langlands.Geometry.FiniteConeClosed` proves that the conic
hull of any finite subset of a real vector space is closed in its module topology.
Its proof uses coefficient elimination, a finite union of independent subcones,
and closed linear embeddings of finite coordinate spaces. It also proves the
Hausdorff property of the module topology by continuous basis coordinates, so
this argument does not need finite dimensionality of the ambient character space.
The helper Markdown gives its full proof route and provenance.

The target Lean/Markdown pair and all its imported files remain unchanged.
