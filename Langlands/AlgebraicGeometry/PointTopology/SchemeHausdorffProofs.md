# Hausdorffness of actual points of separated schemes

Authors: Worker 105 and Worker 266. This proof establishes the separatedness
clause derived from Brian Conrad, *Weil and Grothendieck approaches to adelic
points* (December 31, 2011), Proposition 3.1, printed page 4: "if R is
Hausdorff then X(R) is Hausdorff when X is separated over R". The registered
source is `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

The result uses an arbitrary separated scheme `X` over `Spec R` (separatedness
of the structure morphism `X.hom`) and a Hausdorff commutative topological
local `R`-algebra `S` satisfying `IsOpenUnits S`, with `R` and `S` in a common
arbitrary universe. Only `S` is topologized. The points are actual relative
scheme morphisms `RingPoint R X S` and carry `schemePointTopology`. No finite
type, finite presentation or local compactness assumption is introduced, so
this is a derived generalization of the source clause, which concerns locally
finite type schemes with `S = R`.

## Proof of `t2Space_schemePointTopology`

Let `B` be `Spec R` regarded as an object over itself and `e : X ⟶ B` the
structure morphism. `relativeSchemePullback R e e` is the actual relative
self-product `X ×_B X` and `relativeSchemePullbackIsLimit` its limit property
(`SchemePullbackCharts`). The relative morphism `δ : X ⟶ X ×_B X` has
underlying scheme morphism Mathlib's `pullback.diagonal X.hom`; it is a closed
immersion because `X.hom` is separated, and both projections compose with `δ`
to the identity.

`isClosedEmbedding_schemeClosedPointMap` (`SchemeClosedPointProofs`, which uses
`T2Space S` here) shows that the point map `p ↦ p ≫ δ` has closed image. The
nonaffine pullback point homeomorphism `schemePullbackPointHomeomorph`
(`SchemePullbackProofs`) identifies the points of `X ×_B X` with compatible
pairs of points of `X`, via `p ↦ (p ≫ c.fst, p ≫ c.snd)`. Since `B` is the base
itself, every pair of relative points is compatible over `B`, so the inclusion
`η` of all pairs into compatible pairs is continuous. Composing `η` with the
inverse homeomorphism gives a continuous map `j` from pairs of points to
points of the self-product. The homeomorphism sends `p ≫ δ` to `(p, p)`, so
the preimage under `j` of the closed image of `δ` is exactly the ordinary
diagonal of `RingPoint R X S × RingPoint R X S`. The diagonal is therefore
closed, and `t2_iff_isClosed_diagonal` gives Hausdorffness.

`schemePointHausdorff_proof` packages this result as the exact Prop-valued
target `SchemePointHausdorffProperty R S` from `SchemeHausdorffStatements`,
which is imported unchanged.

## Scope

This proves only the separatedness consequence of Proposition 3.1. The other
assertions of the source, including local compactness, remain separate
obligations of the parent program.
