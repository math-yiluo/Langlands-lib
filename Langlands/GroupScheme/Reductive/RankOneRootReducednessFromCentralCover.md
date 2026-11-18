# Rank-one reducedness from the actual central-cover statement

Worker 799.

This internal derived reduction connects the published
`Langlands.GroupScheme.RankOneCentralCoverStatement.{u}` to the published
rank-one reducedness propositions. Its provenance is the actual-root
transport theorem `eq_or_eq_neg_of_sl2_centralCover` and the field-descent
theorem `rankOneRootReducedness_of_algClosed`. Cover existence remains an
explicit input.

The proposition definition
`RankOneRootReducednessFromCentralCoverStatement.{u}` names the conditional
implication `RankOneCentralCoverStatement.{u} →
RankOneRootReducednessStatement.{u}`. The companion theorems implement this
internal derived reduction. This statement contribution supplies no
exact-target proof receipt for unconditional reducedness or root-datum
existence.

`rankOneAlgClosedRootReducedness_of_centralCover` proves
`RankOneCentralCoverStatement.{u} →
RankOneAlgClosedRootReducednessStatement.{u}`. Fix an algebraically closed
field `k : Type u`, a connected reductive actual group scheme `G`, its
prescribed split maximal torus, and pairwise integral dependence of its
actual adjoint roots. After introducing any two roots, the first root
provides the nonemptiness hypothesis required by the cover statement.
Applying that statement gives the split torus `C`, an actual central
isogeny `SL₂ × C → G`, the compatible torus isogeny, and the commuting
square. The published supplied-cover opposition theorem then makes the
two roots equal or opposite. The affine and local finite type instances
needed for that theorem come from the given reductivity and smoothness.
The proof also covers an empty root set, since the conclusion quantifies
over root memberships and makes no separate nonemptiness assumption.

`rankOneRootReducedness_of_centralCover` inhabits the named conditional
proposition by composing the algebraically closed implication with
`rankOneRootReducedness_of_algClosed`. That published descent transports
the actual roots and their pairwise integral dependence to an algebraic
closure and reflects equality or negation through injective character
pullback. The resulting conclusion is the unchanged
`RankOneRootReducednessStatement.{u}` over arbitrary fields, with no
restriction on characteristic or universe.

Both results retain the cover statement as a hypothesis. They do not
construct a cover or prove unconditional reducedness or root-datum
existence. Their derivation uses supplied-cover root opposition and
actual-root base change. It uses no excluded dynamic-Borel rank-one
proof or global root-line and root-cell consequence of root-datum
existence.
