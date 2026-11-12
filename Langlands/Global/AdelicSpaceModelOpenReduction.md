# Coordinate and stage reductions for adelic openness of algebraic spaces

Authors: Worker 109 and Worker 105. Worker 109 wrote this module. The stage
naturality proof and finite-type base-change instance pattern are adapted
from Worker 105's unreviewed `AdelicSpacePointMapsProof` and
`CoordinatePointMaps` drafts shared on Task 5222
(`360a1cdf-4b68-402e-b087-254b03da61f6`). This module imports only published
prerequisites and the separately submitted `CoordinatePointOpenMap` helper;
it does not import those drafts.

This is derived infrastructure for Conrad's Theorem 5.9, *Weil and
Grothendieck approaches to adelic points*, 31 December 2011, printed p.17.
Registered source: `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The source carries the scheme proof over to algebraic spaces, with the
additional arithmetic input of the space version of Lemma 4.6. The present
module supplies only the coordinate, stage and transport steps of that
argument. Its intermediate open-map lemmas retain their stated hypotheses;
none proves the unconditional Theorem 5.9.

## Constructions

The `curvePlaceSpaceLevelPointHomeomorph` and
`numberFieldSpaceLevelPointHomeomorph` definitions package the actual
coordinate maps of Proposition 5.2 as homeomorphisms. The source has the
published space-level topology, and the target is the product of the
published factor topologies induced from completed-field points. The
coordinate bijections are the published `curvePlaceSpaceLevelPoints` and
`numberFieldSpaceLevelPoints` theorems. The curve construction assumes a
finite constant field, a global function field and a nonempty finite set
of places. The number-field construction uses every infinite place as well
as the finite-place and integral factors.

For each characteristic, `…SpaceLevelModelMap` is actual base change of a
model morphism to a larger integer ring. `…SpaceStagePointHomeomorph`
packages the published stage equivalence as a homeomorphism for its defining
induced topology. `…SpaceSpreadPointHomeomorph` packages the published
spread equivalence as a homeomorphism from model adelic points to the
adelic points of a specified generic fibre. These latter constructions
require no separatedness or finite-type condition: the topologies are
defined through the given equivalences.

## Intrinsic lemmas and implemented proof

At a level, `…SpaceLevel_isOpenMap_of_local` assumes separated finite-type
source and target models, openness on each local factor and surjectivity
at all but finitely many factors. It applies the coordinate openness lemma
from `CoordinatePointOpenMap`, using Proposition 5.2 for the bijections.

At an enlarged stage, `…SpaceStage_isOpenMap_of_local` applies this level
result to the actual base changes of the models and the base-changed
morphism. Separatedness and finite type are stable under base change.
`…SpaceStageEquiv_map` proves naturality of the stage equivalence using
`baseChangeRingPointsEquiv_map`. Conjugation through the stage
homeomorphisms gives the stage conclusion for the original model map.

The general lemma `AdelicSpaceOpenReduction.isOpenMap_of_stages` uses the
continuous map from the disjoint union of source stages to the final
space. Its explicit coverage assumption makes that map surjective.
Every composite with a source stage is open by the compatibility square,
the stage-map openness hypothesis and openness of the corresponding
target-stage inclusion. `IsOpenMap.of_comp` then proves the conclusion.
`…SpaceAdele_isOpenMap_of_stages` specializes this to the actual stage
maps of the model adelic points. It retains both source coverage and
target-stage openness as hypotheses; the unproved adelic-space topology
package is not silently assumed.

Finally `…SpaceGenericFiberEquiv_map` proves naturality of the actual
identification of model adelic points with generic-fibre adelic points.
`…SpaceSpreadEquiv_map_of_model` converts a square of morphisms between the
actual generic fibres into a square of point maps. Then
`…SpaceSpread_isOpenMap_of_model` transports an open model point map to
the specified generic fibres through the two spread homeomorphisms.
Its model-square premise is a categorical equality, rather than an
assumed identity of topological conclusions.

## Remaining obligations

This module supplies no existence of compatible smooth models, no local
smooth-openness theorem for general algebraic spaces, and no eventual
component-surjectivity theorem. It also supplies no independence of the
spread topology when the source and target come from different integer
rings. Those inputs remain necessary to apply these constructions to the
unchanged `AdelicSpaceSpreadSmoothOpenStatement` in full generality.
