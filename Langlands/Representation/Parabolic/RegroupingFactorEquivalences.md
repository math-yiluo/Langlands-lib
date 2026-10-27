# Factor identifications for ordered three-block regrouping

Author: Worker 645.

This internal adapter module supports the literal three-block associativity
consumer. It constructs actual equivalences of representation actions and an
ordered family of three bundled smooth representations. It does not assume or
prove a regrouping theorem.

`FiniteTensor.rankCastRepresentationEquiv F T h A`, for `h : r = s` and a smooth
representation `A` of `GL_s`, presents the published
`rankCastLinearEquiv F T h A` as an actual representation equivalence. Its source
is the action of `A` precomposed with the entry-preserving reindexing from
`GL_r` to `GL_s`; its target is the action on the categorically transported
object `h.symm ▸ A`. The intertwining law is exactly the published
`rankCastLinearEquiv_action`.

`T.singleBlockTransportedProductEquiv B hB A` applies when `B` has total rank
`n` and one block, and `A` is a smooth representation of `GL_n`. Each input
factor is the categorical transport of `A` along the equality of that block's
rank with `n`. The constructed equivalence identifies the actual normalized
product induction of this family with `A`. Its forward map first evaluates the
induced function at the identity and applies the singleton tensor map. It then
uses the inverse of the published rank-transport carrier map.

The proof composes `singleBlockNormalizedProductEquiv` with the inverse rank
equivalence, precomposed with the inverse matrix reindexing. The two group
reindexings cancel. Thus the target action is exactly the original action of
`A`, with no residual rank precomposition.

`Parabolic.threeBlockSmoothFamily` places three smooth representations of
ranks `C`, `A`, and `B` into the dependent family with literal ranks
`![C,A,B]`. Its values at `0`, `1`, and `2` are definitionally the original
three objects. All carriers share the independently quantified universe `uV`.

The provenance is internal composition of the published singleton evaluation
and rank-transport constructions, together with finite dependent case
analysis. This module supplies no three-block geometry or rank transport of an
induced representation, and it does not prove common-universe associativity
or the closed heterogeneous target.
