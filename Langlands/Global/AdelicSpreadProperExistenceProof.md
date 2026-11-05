# Proper morphisms over actual arithmetic integer rings

`Langlands.Global.adelicSpreadProperExistence` proves the unchanged
`Langlands.Global.AdelicSpreadProperExistenceStatement` in arbitrary common
universe `u`, with both original arithmetic ring systems. Worker 208 authored
the proof; Worker 1557 checked it against the published prerequisites and
prepared this proof-only pair for independent review. All predecessors are
imported by Lean name.

The cone-projection and pullback-coherence helpers adapt Worker 208's earlier
closed-immersion spread proof. They descend the prescribed generic morphism
using `exists_level_morphism`, retain its cone square and identify its generic
base change with the prescribed morphism through canonical pullback isomorphisms.

For two finite-type models over the same integer ring, descend the prescribed
proper generic morphism to a finite superlevel. Its actual generic base change
is proper by the coherent isomorphisms. Apply
`curvePlaceSpreadEventualProperness` or `numberFieldSpreadEventualProperness`
to enlarge again until the model morphism is proper. Target separation is
preserved by base change, and properness of the morphism implies source
separation. Finite type and quasi-compactness are preserved by base change.
Naturality of the iterated pullback isomorphisms proves the required commuting
generic-fibre equation, including both enlargement steps.

For an arbitrary field morphism in the target, properness and the given target
properties first imply that its source is separated and of finite type.
Choose a separated arithmetic spread for the target above the prescribed
initial level, then one for the source above that level. Base-change the target
model to the latter level and apply the same-base construction. Transitivity
of finite-set containment gives a final level containing the original set.
No affineness, nonempty initial level, finite constant field or separability
hypothesis is added.

The general properness-descent input imported through the eventual-properness
proof is Worker 105's independent development. The arithmetic colimit,
separated-model existence and eventual-properness proofs are imported, not
resubmitted here. The source is Brian Conrad, *Weil and Grothendieck approaches to adelic
points* (December 31, 2011), printed pp.5–6, Theorem 3.4(1)–(2) and
Remark 3.5, and printed p.11, Proposition 4.4, first proof paragraph.
It is registered as `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
This derived arithmetic specialization uses the proved Noetherianity and
actual integer-algebra colimits to cover perfect, possibly infinite constants,
possibly inseparable rational-function extensions and empty initial sets,
as explained in the unchanged target Markdown. This proof supplies the model choice at the
start of Conrad's Proposition 4.4; intrinsic adelic properness, compactness,
eventual stabilization and the remaining whole-paper obligations are separate.

The model-cone projection, morphism-descent and pullback-composition helpers are
shared with the related spread proofs through
[`AdelicSpreadModelMorphisms`](AdelicSpreadModelMorphisms.md). This integration
consolidation preserves their definitions, hypotheses and conclusions.
