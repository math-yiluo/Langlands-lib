# Cutting the top cuspidal off products of segment heads

Module `Langlands.Representation.Classification.MoeglinWaldspurgerListCut`, namespace
`Langlands.MoeglinWaldspurger.Derivation`. Internal infrastructure; the only mathematical input
is the published head-cut embedding (Zelevinsky's embedding of the Langlands quotient of a
segment into the product of the quotients of a consecutive cut), used here with a one-point top
piece. Write `A_c` for the chosen supercuspidal representative `cuspRep F T ρ x c` of
`ν^{x+c} ρ`.

## Segment-level statements

* `singleton_isSegmentHead`: a supercuspidal representative of `κ`, transported to the degree
  of the one-term segment, is a segment head of that segment. This reproduces a four-line
  Library proof (`singletonSegmentInducedEquiv` and `isIrreducibleHead_self`) to avoid a heavy
  import.
* `castIso_heads_of_eq`: segment heads of equal segments agree up to rank transport. Both are
  isomorphic to `T.segmentHead` (`IsSegmentHead.nonempty_iso_segmentHead`).
* `headCut_embeds` and `headCut_embeds'`: the head of a segment `⟨κ, 1 + b⟩` with `b > 0`
  embeds into `A × Z₂`. Here `A` represents `κ.twist b`, the top cuspidal, and `Z₂` is a head of
  `⟨κ, b⟩`. Proof: apply `SegmentHeadCut.headCutEmbedding` with cut `(1, b)`. Its first factor
  is the head of the one-term segment of `κ.twist b`, given by `singleton_isSegmentHead`. The
  resulting injective intertwining map into the rank-transported product becomes an `Embeds`
  statement via `embeds_of_isSubrepresentation_rankCast`, and the transported block is replaced
  by `A` via `castIso_castRank`. The primed form transports along equalities of segments.

## Interval-level statements

* `shortR I h`: for `I = [i, e]` with `i < e`, the interval `[i, e - 1]`.
* `segHead_cut`: for `I = [i, c]` with `i < c`, `L([i, c]) ↪ A_c × L([i, c - 1])`. Proof:
  `headCut_embeds'` with `b` the length of `[i, c - 1]`. The representative condition is proved
  at the level of classes with `supercuspidalClassRealPowerTwist_add`, using
  `b + (x + i) = x + c` in `ℝ`.
* `segHead_point`: the head of `[c, c]` is `A_c` up to rank transport.
  `pointBlock_isSegmentHead` shows the transported representative is a head of the point
  segment, and `castIso_heads_of_eq` compares the two heads.
* `castIso_segHead_swap`: if the realized segment of `I` is not linked with the point `[c, c]`,
  then `L(I) × A_c ≅ A_c × L(I)`. Proof: `castIso_head_swap` of `MoeglinWaldspurgerHeadMoves`,
  with linkedness translated by `realize_isLinked_iff`.

## Lists

* `posOrIrr_listProd`: `listProd` preserves `PosOrIrr`.
* `shortList l`: every interval of `l` shortened at its right end, one-point intervals dropped.
* `cut_listProd` (**cutting a list of heads**): if every interval of `l` ends at `c` and `Y`
  satisfies `PosOrIrr`, then `listProd l Y ↪ A_c^{|l|} × listProd (shortList l) Y` up to rank
  transport. Proof by induction on `l`. For `I :: l`, the induction hypothesis gives
  `L(I) × listProd l Y ↪ L(I) × (A_c^k × Y')`. This is `A_c^k × (L(I) × Y')` by
  `castIso_commute`, since `[i, c]` and `[c, c]` are not linked. If `i < c`, `segHead_cut` and
  `castIso_assoc'` give `L(I) × Y' ↪ A_c × (L([i, c-1]) × Y')`. If `i = c`, `segHead_point`
  gives `L(I) × Y' ≅ A_c × Y'`. In both cases `castIso_iterProd_shift` absorbs the new factor
  `A_c`.
