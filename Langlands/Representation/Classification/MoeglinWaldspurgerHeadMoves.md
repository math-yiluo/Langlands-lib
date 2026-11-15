# Swapping unlinked segment heads in a binary product

This module is internal infrastructure for the derivative-comparison proof of the
Moeglin–Waldspurger algorithm. It contains no new mathematics beyond the published
commutation of two unlinked segment heads; it only moves that statement from segment-product
data to binary products, up to rank transport (`CastIso`, see
`MoeglinWaldspurgerCastCalculus`).

## Statements

* `castIso_blocks_of_eq`: equal block indices give rank-transport-isomorphic blocks.
* `castIso_induced_two`: for a segment-product datum `d` with exactly two blocks, the
  induced representation `d.induced` is, up to rank transport, the binary normalized product
  of its head block and its single tail block.
* `swap_cast_zero`, `swap_cast_one`: the adjacent transposition of a two-element index type
  exchanges the head index and the tail index (index bookkeeping after casting along
  `m = 0 + 2`).
* `castIso_head_swap`: if `L` is the Langlands head of a segment `Γ`, `A` the Langlands head of
  a segment `κ`, and `Γ` and `κ` are not linked, then `L × A` and `A × L` are isomorphic up to
  rank transport.

## Proofs

`castIso_induced_two` splits `d` with `SegmentProductSplit.nonempty_iso_binary` into its head
block times the induced representation of the tail datum, and identifies the latter, a
one-block datum, with its block by `SegmentProductOrderedAssembly.singletonIso`; the rank casts
introduced by these isomorphisms are absorbed with `castIso_generalLinearRankCast`, and the two
pieces are combined with the binary congruence `CastIso.binary`.

The two index lemmas are proved by substituting `m = 2` and computing.

For `castIso_head_swap`, the two-block datum `d = cons Γ L (cons κ A empty)` has segment heads
as blocks. The published theorem `twoSegmentHeadCommutation` gives an isomorphism between
`d.induced` and the induced representation of `d` permuted by the adjacent swap. Both sides are
rewritten as binary products by `castIso_induced_two`; for the permuted datum the head and
tail blocks are the tail and head blocks of `d`, which is the content of the two index lemmas
(after unfolding `BlockShape.adjacentSwap`, `headIndex` and `tailIndex`), transported by
`castIso_blocks_of_eq`. Chaining these rank-transport isomorphisms gives the claim.
