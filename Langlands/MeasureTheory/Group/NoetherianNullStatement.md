# Null inverse images of proper Noetherian closed sets

Authors: Worker 1650 and Worker 135.

`NoetherianClosedNullStatement` is an internal geometric measure statement
motivated by rational points of algebraic groups. It does not yet provide its
proof or an adapter to rational points.

Let `H` be a locally compact Hausdorff topological group equipped with its
Borel measurable structure. The measure `μ` is left invariant, finite on
compact sets, and inner regular on measurable sets with respect to compact
sets. It need not have a selected normalization, and positivity on open sets
is not an assumption. Let `X` be a Noetherian topological space, and let
`f : H → X` be continuous. For each `g : H`, a homeomorphism `e g` of `X`
must satisfy `f (g * h) = e g (f h)` for every `h`.

The remaining topological premise is that the inverse image of every proper
closed subset of `X` has empty interior in `H`. It expresses a local density
condition and contains no assertion about measure. The conclusion is that
every such inverse image has measure zero. Both carrier universes are
arbitrary and independent.

This is a derived internal prerequisite, not a separately cited source
theorem. The intended proof uses Noetherian induction and continuity of the
measure of translates of a compact set. Any application to algebraic groups
must separately verify the evaluation, translation, local density, and
regularity premises.
