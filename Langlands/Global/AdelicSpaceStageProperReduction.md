# Properness on arithmetic levels and stages

This derived reduction implements the finite-stage properness argument for the
actual algebraic-space point topologies. Its inputs are
`LocalFieldProperPointMapStatement` and `ProperSchemeBaseChangeStatement`,
both kept explicit. It supplies no proof of either geometric input.

For separated finite-type models `X`, `Y` and a proper model morphism `f`,
`isProperMap_genericFiber` first changes the base to a local field. The two
models remain quasi-separated and locally of finite type; the base-change
input preserves properness of `f`, and the local proper-point input gives
properness of the resulting map on field-valued points.

The factor lemmas handle every actual coordinate. At field coordinates, the
coefficient map is bijective, so the generic-fibre proper map transfers across
the actual field-valued point homeomorphisms. At integral coordinates, the
source factor is compact and the target is Hausdorff by
`AdelicSpaceLevelTopologyProof`; induced-topology functoriality gives
continuity and hence properness. The number-field argument includes every
infinite place as well as finite places inside and outside `S`.

The level lemmas use the coordinate bijections for separated finite-type
models and properness of arbitrary products. The stage lemmas base change
the model to each enlarged ring of integers and apply the level result.
The published stage point homeomorphisms and their naturality transfer
properness back to the defining stage topology. In the curve case,
nonemptiness of `S` ensures nonemptiness of every larger level `T`.

`curvePlaceSpaceStageProperMap` and `numberFieldSpaceStageProperMap` bundle
the actual stage function `RingPoints.map f` as a continuous map together
with its properness proof. Their underlying functions are definitionally
the model's point maps on the indicated stages. Both constructions retain
the two geometric inputs and all hypotheses of their respective stage
properness lemmas.

The contextual source is Conrad, *Weil and Grothendieck approaches to adelic
points* (2011), printed p.11 and pp.16–17. The implemented proof is a
deduction from the published coordinate/stage constructions, compact
integral-factor results, and the two explicit local geometric inputs.
It proves the properness half of the finite-stage conclusion conditional
on those inputs. Exact full-adele preimages and the final unconditional
`AdelicSpaceProperStagesStatement` are separate obligations.
