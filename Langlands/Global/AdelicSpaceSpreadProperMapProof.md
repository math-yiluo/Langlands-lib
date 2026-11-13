# Proper maps of algebraic spaces on adelic points

Author: Worker 108.

`Langlands.Global.adelicSpaceSpreadProperMap` proves exactly the published
`Langlands.Global.AdelicSpaceSpreadProperMapStatement.{u}` in arbitrary common
universe `u`, with no additional premise. A proper morphism of the field
algebraic spaces induces a topologically proper map on their actual adelic
points, for every independently supplied pair of separated finite-type models.

The function-field clause retains finite constants, the compatible
rational-function-field action and the nonempty finite sets of places.
The number-field clause allows empty finite sets of finite places and retains
all infinite factors in the full adele ring. Both clauses use the unchanged
spread topologies in
[`AdelicSpaceSpreadMapStatement`](AdelicSpaceSpreadMapStatement.md).
The target's finite-type-model scope is retained; the result makes no extension
to the merely locally finite-type scope of the printed Proposition 5.8.

## Implemented proof

The private lemma `AdelicSpaceSpreadProperMapReduction.proper_of_stages`
passes from proper stage maps to a proper full-point map. Write `f : A → B`
for the full map, `aᵢ` and `bᵢ` for the stage maps, and `gᵢ` for the map on
stage points. Its hypotheses are continuity of `f` and each `aᵢ`, injectivity
of each `bᵢ`, coverage of `B` by the target stages, the commuting squares,
the exact equality `f ⁻¹' range bᵢ = range aᵢ`, the final topology on `B`,
and properness of each `gᵢ`.

For a closed set `C ⊆ A`, the commuting square, exact preimage equality and
injectivity give
`bᵢ ⁻¹' (f '' C) = gᵢ '' (aᵢ ⁻¹' C)`.
The right side is closed by continuity of `aᵢ` and closedness of the proper
stage map. The final topology makes `f '' C` closed. Every `y ∈ B` lies
in some target stage, say `y = bᵢ(z)`, and the same hypotheses identify
the full fibre with `aᵢ '' (gᵢ ⁻¹' {z})`. It is a continuous image of a
compact stage fibre. Mathlib's
`isProperMap_iff_isClosedMap_and_compact_fibers` then proves properness.

The two `*_fixedModel_proper` lemmas apply this argument to the actual
arithmetic stage and full-adele point carriers for a chosen proper model
morphism. The point-topology package supplies continuity of the full map,
continuous source stage maps, injective target stage maps and stage coverage.
The proper-stage package supplies properness of the stage maps and the exact
full-adele preimage identities. Coefficient naturality supplies the commuting
squares. The defined full-point topology is the required supremum of
coinduced stage topologies.

The two `*_spread_proper_of_model` lemmas transport this properness to the
field-point carriers. The spread equivalences, with their defining induced
topologies, are homeomorphisms. Naturality of the actual generic-fibre section
equivalences and the prescribed commuting generic-fibre square identify the
conjugated model map with `RingPoints.map g`. Composition with the two
homeomorphisms preserves properness.

`adelicSpaceSpreadProperMap_of_inputs` obtains a common integer ring, separated
finite-type models, a proper model morphism and its exact square from the
proper-model package. Topology independence rewrites the source and target
topologies from the original independent models to those of the chosen models.
The preceding transport lemmas then prove both arithmetic clauses.

The remaining named reductions supply the published inputs in order:

- `adelicSpaceSpreadProperMap_of_arithmeticInputs` supplies
  `adelicSpacePointTopology` from `AdelicSpacePointTopologyTheorem`.
- `adelicSpaceSpreadProperMap_of_properModel` also supplies
  `adelicSpaceProperStages` from `AdelicSpaceProperStagesProof`.
- The entry theorem `adelicSpaceSpreadProperMap` supplies
  `adelicSpaceProperModel` from `AdelicSpaceProperModelProof`.

Thus all premises of the assembly are discharged by imported proofs, and the
entry theorem has exactly the unchanged published proposition as its type.

## Provenance

The original source is Brian Conrad, *Weil and Grothendieck approaches to
adelic points* (December 31, 2011), registered as
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`,
printed p.11, proof of Proposition 4.4; p.13, extension of Theorem 3.4 to
algebraic spaces; and p.17, the paragraph before Proposition 5.8 and the
proposition itself. Conrad transfers the scheme proper-map argument using
Corollary 5.6. The imported proper-stage proof implements the local and integral
steps, while the imported proper-model proof implements spreading.

The final-topology lemma and spread transport follow the published scheme
implementations `AdelicFixedModelProperMapProof` and
`AdelicSpreadProperMapProof` by Worker 208, with the latter prepared for review
by Worker 1557. Worker 108 adapted this argument to algebraic-space sections.
The topology package is reused from `AdelicSpacePointTopologyTheorem`, the
proper-stage proof from Workers 128 and 101, and the proper-model proof from
Workers 129 and 157. These predecessors are imported by Lean name.
The helper names and the conditional reductions are internal derived
packaging of the implemented argument.
