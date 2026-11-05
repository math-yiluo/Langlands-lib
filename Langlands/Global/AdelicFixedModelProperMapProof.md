# Properness of full-adele fixed-model maps

## Result and scope

`Langlands.Global.adelicFixedModelProperMap` proves exactly
`Langlands.Global.AdelicFixedModelProperMapStatement` in arbitrary common
universe `u`. The two constituent theorems are
`curvePlaceFixedModel_proper` and `numberFieldFixedModel_proper`.
For a proper morphism of models over the original outside-S integer ring
with separated finite-type target, literal postcomposition on actual
full-adele relative scheme points is a topologically proper map for the
previously defined fixed-model final topologies.

The function-field clause retains finite constants, the specified compatible
finite extension of the rational-function field and its scalar tower, with
no separability assumption. The number-field clause retains every infinite
completion. Both clauses allow every finite initial level, including the
empty level, and arbitrary nonaffine models. The target hypotheses are
`LocallyOfFiniteType`, `QuasiCompact` and `IsSeparated` for its structure
morphism, together with `IsProper` for the supplied model morphism.
The proof adds no hypothesis to the statement and does not change its
point carriers, coefficient maps or topologies.

## Implemented topological argument

The private helper `isProperMap_of_final_stages` considers a continuous map
`f : A → B`, source stage maps `aᵢ`, injective target stage maps `bᵢ`, and
commuting stage maps `gᵢ`. It assumes continuous source stage maps, proper
stage maps, a cover of `B` by the target stage images, the final-topology
closed-set criterion on `B`, and the exact preimage identity
`f ⁻¹' range bᵢ = range aᵢ`.

For a closed subset `C` of `A`, these identities and target-stage
injectivity give
`bᵢ ⁻¹' (f '' C) = gᵢ '' (aᵢ ⁻¹' C)`.
The right side is closed because `aᵢ` is continuous and `gᵢ` is a closed
map. The target's final-topology criterion therefore makes `f '' C`
closed. For a target point written `bᵢ(y)`, the full fibre equals
`aᵢ '' (gᵢ ⁻¹' {y})`, again by the exact preimage identity and injectivity.
This is a continuous image of a compact fibre, hence compact.
Mathlib's `isProperMap_iff_isClosedMap_and_compact_fibers` now proves
properness. This helper needs no open-stage assertion or separation
axiom on the ambient spaces.

The private `ringPointCoconeTopology_isClosed_iff` obtains the required
closed-set criterion by taking complements in the existing open-set
criterion for the cocone topology.

## Arithmetic stage inputs

The following constructions are implemented separately for the curve-place
and number-field systems.

For a containing finite level `T`, the original models are pulled back
from the outside-S integer ring `C` to the outside-T integer ring `D`.
Properness of the model morphism and the target structure hypotheses
survive this base change.

The private `ringPointBaseChangeEquiv_symm_changeRing` proves coefficient
naturality of the inverse point equivalence: its underlying morphism is
the first pullback projection, so the equality follows from associativity.
The forward naturality theorem follows by injectivity of the inverse
equivalence. The helper `ringPointBaseChange_preimage` then transports
an exact coefficient-range preimage identity from the base-changed models
back to the original models.

The arithmetic `*_stage_preimage` lemmas install the actual inclusion
`C → D`, the actual `D`-actions on the level-T ring and the full adele
ring, and their compatible scalar towers. They apply
`adelicFullLevelPreimage` to the base-changed proper model morphism at
`T`, and transport its identity with `ringPointBaseChange_preimage`.
Thus the full-point map pulls each target stage image back exactly to
the corresponding source stage image, even though all stages retain the
original `C`-relative point description.

For `*_stage_injective`, every local level factor is reduced: it is a
completion field or a completed valuation ring. The actual product-ring
equivalence therefore makes the level ring reduced. Its literal inclusion
in the full adele ring is injective, so
`schemeSeparatedCoefficientInjectivity_proof` gives injectivity on target
points. This step uses separatedness of the target; it does not use its
quasi-compactness.

For `*_stage_proper`, `adelicLevelModelProperMap` proves properness of
postcomposition on the base-changed level-T model points. The existing
`curvePlaceFixedModelPointHomeomorph` or
`numberFieldFixedModelPointHomeomorph`, together with the corresponding
point-equivalence naturality theorem, conjugates this map to the literal
fixed-base stage postcomposition. Properness is preserved under these
homeomorphisms.

Finally, the two public arithmetic theorems instantiate
`isProperMap_of_final_stages`. Full-point continuity comes from the
fixed-model functoriality proof. Source-stage continuity is the canonical
continuity supplied by the cocone topology. Associativity gives the
commuting squares, and `adelicFixedModelFiniteType` gives the target-stage
cover. The preceding lemmas supply target injectivity, exact stage
preimages and stage properness. The main theorem pairs these two proofs.

## Provenance and remaining obligations

The original source is Brian Conrad, *Weil and Grothendieck approaches to
adelic points* (December 31, 2011), registered as
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`,
printed p.11, Proposition 4.4, first two proof paragraphs. This proof
implements the derived chosen-model conclusion isolated by the unchanged
statement. The final-topology closed-map and compact-fibre argument above
is an internal proof of the passage from arithmetic stages to full points.

The imported level properness proof uses properness over the local fields
and compact integral source point spaces with Hausdorff targets. It avoids
the false identification of integral and field points of the target in
the printed proof, as explained in the statement's Markdown. The imported
full-level preimage proof supplies the valid valuative preimage equality.

This result assumes a proper arithmetic model morphism has already been
chosen. Spreading an arbitrary generic-fibre proper morphism, comparison
with the intrinsic generic-fibre adelic topology, compactness and eventual
stabilization in Proposition 4.4, and the other sections of the paper
remain separate obligations. Worker 208 authored this proof pair;
prerequisite results are imported by Lean name.
