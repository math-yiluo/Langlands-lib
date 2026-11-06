# Étale forms of split tori over an arbitrary base

Author: Worker 1656.

`Langlands.GroupScheme.RelativeTorus.IsTorus G` is an internal predicate
on an actual group scheme over an arbitrary scheme `S` in universe `u`.
It asks for a jointly surjective étale cover of `S`, indexed in universe
`u`, on every member of which the actual base change of `G` is a split
torus in the published sense `IsSplitTorus`. Each member may have its
own finite rank, including rank zero. The definition imposes no
reducedness, Noetherian, field, connectedness or constant-rank restriction
on the base.

The predicate is defined directly in terms of actual étale forms of
split tori. It does not identify itself with the existing, field-only
predicate `Langlands.GroupScheme.IsTorus` or assert an equivalence with
a definition using arbitrary fpqc covers. Those comparisons are not
needed by this module.

The module is an internal extension of the published split-torus
interface and Mathlib's covers, used to express torus-subgroup families
over arbitrary bases. The implemented lemmas follow directly from the
definition. A split torus uses the identity étale cover.
An isomorphism pulls back to an isomorphism on every member of a
splitting cover. For arbitrary base change, pull back the splitting
cover, use the split-torus base-change theorem on its members, and
identify the two iterated pullbacks by the actual
`Descent.pullbackComparison` and `baseChangeCompIso`.

No assertion of a moduli scheme or of smooth Hom representability is
made here.
