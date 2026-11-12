# Reduction of finite-extension point embeddings to complete fields

Author: Worker 157.

This internal unit formalizes the completion reduction on printed p.19 of
Brian Conrad, *Weil and Grothendieck approaches to adelic points* (December 31,
2011), registered source `conrad-2011-weil-grothendieck-adelic-points`,
SHA-256 `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
It is a reduction of the finite-extension embedding assertion. The complete-field
case is an explicit premise, and is not proved by this module.

`fieldExtensionPointMap` is the point map in the published
`HenselianFiniteExtensionPointEmbeddingStatement`: coefficient change followed
by the inverse of `baseChangeRingPointsEquiv`. The module constructs base-changed
finite-type étale charts, proves their compatibility with this point map, and
uses the existing scheme coefficient embedding and scheme base-change
homeomorphism to prove continuity. Continuity needs neither henselianity nor
finiteness of the normed extension. Scheme points embed for every normed field
extension; this is used only on charts and is not asserted here for general
algebraic spaces.

`RingPoints.changeRing_comp` and `fieldExtensionPointMap_tower` prove the
commuting identities for successive coefficient changes. The latter uses the
published `towerIso` between iterated and direct base changes.
`IsLocallySeparated.baseChange` supplies preservation of the diagonal immersion;
quasi-separatedness and local finite type are preserved by the already published
base-change results.

`CompleteFiniteExtensionPointEmbeddingStatement` is an internal Prop-valued
target for finite normed extensions of complete fields, with the same
quasi-separated, locally separated and locally finite-type spaces as the
original target. It asserts an embedding, without an image-closedness conclusion.
`henselianFiniteExtensionPointEmbedding_of_complete` proves that this target
implies the full published henselian finite-extension statement.

The reduction installs the canonical normed algebra on the completions from
`FiniteExtensionCompletion`. Its finiteness theorem makes the completed extension
finite, including in the inseparable case. Proposition 5.11(2), already proved
as `henselianCompletionPointEmbedding`, embeds points over each original
henselian field into points over its completion. The assumed complete-field
embedding composes with the first embedding. The tower identities identify
this composite with the original extension map followed by the second
completion embedding, up to the homeomorphisms supplied by `towerIso`.
Cancelling that second embedding proves the desired embedding.

This implements Conrad's reduction without using the false unrestricted
Proposition 5.11(1). An eventual complete-field proof may use the corrected
module-topology version of Proposition 5.11(1); no such comparison is assumed
implicitly here.
