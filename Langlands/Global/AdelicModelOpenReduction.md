# From local maps to actual adelic openness

Authors: Worker 208 and Worker 1525.

`adelicModelOpenReduction` proves exactly
`Langlands.Global.AdelicModelOpenReductionStatement.{u}`, for an arbitrary
universe `u`. Its declared type is that proposition, and the proof is the
pair of the two arithmetic theorems described below. The file imports the
target without changing its Lean or Markdown file.

## Source and route

This is the topological reduction in the proof of Theorem 4.5 in Brian
Conrad, *Weil and Grothendieck approaches to adelic points* (December 31,
2011), printed p.12, first two proof paragraphs. Conrad varies the finite
set of places T containing S, so it suffices to prove openness on each
stage of S-integral adelic points. He writes the stage map as a product of
the local point maps. By the definition of the product topology, openness
then follows from openness of every local map and surjectivity of the
integral point maps at all but finitely many places.

The Lean proof follows this route with the actual Library rings, scheme
morphisms and independently defined topologies, with two differences of
presentation. First, the local hypothesis asserts openness of the point map
over every factor of the level, including the integral factors. Conrad
instead derives the integral case from the map on points over the local
field. Second, the passage from stages to the full adelic points is a
separate argument about the existing final topology on the cocone points.
The local openness and eventual-surjectivity assertions are hypotheses
here; they are not proved in this file.

## Products of local point maps

`isOpenMap_localProduct_postcomp` works over any commutative ring A. The
coefficients are a family R i of commutative topological A-algebras that
are local rings with open units. X and Y are schemes over Spec A whose
underlying spaces are compact and quasi-separated, and f is a morphism
between them. Suppose that the point maps of f over every R i are open for
`schemePointTopology` and surjective for cofinitely many i. Then the point
map of f over the product ring is open for `localProductPointTopology` on
both sides. This lemma assumes neither finite type nor separatedness.

The proof shows that `productPointMap` is a homeomorphism for X and for Y.
It is inducing by `productPointMap_isInducing_localProductPointTopology`,
injective by `productPointMap_injective` and surjective by
`productPointMap_surjective`. Mathlib's `IsOpenMap.piMap` shows that the
coordinatewise map between the products of local point spaces is open,
using the cofinite-surjectivity hypothesis exactly as stated. The equality
`productPointMap_natural` identifies this coordinatewise map, conjugated by
the two homeomorphisms, with postcomposition by f. Hence postcomposition
by f is open.

## Passage from stages to cocone points

`isOpenMap_ringPointCocone_postcomp` concerns a diagram D of commutative
A-algebras and a cocone c over it. Arbitrary topologies on the stage point
sets of X and Y give the existing `ringPointCoconeTopology` on points over
c.pt. This is the final topology of the stage maps. The hypotheses are:

- every point of X over c.pt comes from a point over some stage;
- postcomposition by f is open on each stage;
- each stage map of Y into its cocone points is open.

The lemma assumes no filteredness, colimit property or geometric finiteness.
The map from the disjoint union of the source stages to the cocone points
is continuous by `ringPointCoconeTopology_continuous_ι` and surjective by
the first hypothesis. On each summand, the composite with postcomposition
by f equals the target stage map after the stage map of f, by associativity
of composition of scheme morphisms. This composite is open, so
`isOpenMap_sigma` and `IsOpenMap.of_comp` give openness on cocone points.

## The arithmetic stages

`curvePlaceFixedModelStage_isOpenMap` and
`numberFieldFixedModelStage_isOpenMap` treat one finite superlevel T
containing S, over the original ring of S-integers. They transport the
product lemma along the published homeomorphisms
`FixedModelLocalProduct.curveStageHomeomorph` and
`FixedModelLocalProduct.numberFieldStageHomeomorph`. These identify the
stage topology with `localProductPointTopology` over the actual level
factors. The identities `curveStageHomeomorph_natural` and
`numberFieldStageHomeomorph_natural` show that the homeomorphisms commute
with postcomposition by f. Quasi-compactness and separatedness of X and Y
over the affine base give the compact, quasi-separated underlying spaces
that the product lemma requires. These two lemmas do not assume local
finite type.

The function-field factors at level T are the completions at the places in
T and the completed integer rings at the places outside T. The number-field
factors are the completions at all infinite places, the completions at the
finite places in T and the completed integer rings at the finite places
outside T. So every original infinite factor is retained.

## The full adelic points

`curvePlaceFixedModelAdele_isOpenMap_of_local` and
`numberFieldFixedModelAdele_isOpenMap_of_local` add the assumption that X
and Y are locally of finite type. The function-field theorem also keeps the
compatible scalar tower from k through RatFunc k to F. At each finite
superlevel T, they assume openness at every factor and surjectivity at
cofinitely many factors. The finite exceptional set may depend on T, and
the exceptional maps need not be surjective. They conclude that
postcomposition by f is open on the actual full fixed-model adelic point
spaces, with the final topologies `curvePlaceFixedModelAdelePointTopology`
and `numberFieldFixedModelAdelePointTopology`. Both are instances of
`ringPointCoconeTopology`.

These theorems apply the cocone lemma to the actual level diagram and
adelic cocone. The stage hypothesis is the stage theorem above. The covering
hypothesis is the first clause of the published `adelicFixedModelFiniteType`
for X. The open target stage maps come from the first clause of the
published `adelicFixedModelColimitOpen` for Y. The models may be nonaffine.

## Scope

This file proves only the topological passage. It does not prove openness
of local point maps for smooth morphisms, spreading of a morphism of generic
fibres, the Lang-Weil estimate or eventual surjectivity on integral points.
It does not claim the full Theorem 4.5. Those remain obligations of the
parent formalization.
