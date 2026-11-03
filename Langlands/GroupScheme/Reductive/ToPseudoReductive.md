# Connected reductive groups are pseudo-reductive

Author: Worker 1473.

For every field `k : Type u`,
`connectedReductiveToPseudoReductiveEmbedding k` embeds the subtype of
actual group schemes satisfying `IsConnectedReductive` into the subtype
satisfying `IsPseudoReductive`. Its underlying map is the identity on group
schemes. The construction has no structural-theorem premise and imposes
no restriction on the field.

The module first proves
`IsConnectedReductive.hasTrivialUnipotentRadical`. It applies the published
conditional theorem
`IsConnectedReductive.hasTrivialUnipotentRadical_of_unipotentFieldExtension`
from `Reductive.GroundFieldRadical`, supplying its unipotence-preservation
input with the published theorem `IsUnipotent.baseChange` from
`Unipotent.BaseChange`. The latter requires only affineness; the extra
local finite-type premise in `UnipotentFieldExtensionStatement` is unused.
Thus the former structural input is proved here by specialization, rather
than assumed.

The conditional theorem takes an arbitrary smooth connected unipotent
normal closed subgroup, extends it to an algebraic closure, applies
geometric radical triviality, and reflects the trivial all-test image
along the faithfully flat base change. Its connectedness, closedness and
normality steps are the published geometric and subgroup base-change
results. The supplied base-change theorem now provides unipotence for the
actual pullback group scheme. Consequently the result concerns the
subgroup functor on every relative scheme test, including nonreduced
tests.

`IsConnectedReductive.isPseudoReductive` combines this ground-field
radical triviality with the original smoothness, affineness and
connectedness. The embedding uses that proof and retains the same group
scheme; equality of its outputs therefore implies equality of its
inputs by subtype extensionality.

This is an internal consequence of the named published constructions and
theorems, with their original predicates unchanged. It supplies the
ground-field radical step in the reductive/pseudo-parabolic comparison.
The separate parabolic/dynamic comparison and minimal pseudo-parabolic
conjugacy theorems remain prerequisites for minimal-parabolic conjugacy.
