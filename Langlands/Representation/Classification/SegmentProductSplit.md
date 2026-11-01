# Splitting a segment product into its first factor and its tail

Module `Langlands.Representation.Classification.SegmentProductSplit`,
namespace `Langlands.Classification.SegmentProductSplit`.

Let `d` be a segment-product datum with at least two segments. Its actual
product `d.induced = π_1 × π_2 × … × π_r` is isomorphic, after the rank
transport `deg Δ_1 + (deg Δ_2 + … + deg Δ_r) = n`, to the binary normalized
product `π_1 × (π_2 × … × π_r)`. The proof of Zelevinsky's Theorem 6.2 uses
this to induct on the number of segments.

## Provenance

This is internal derived material. It packages the published head/tail
regrouping isomorphism `PadicField.TopologicalData.headTailProductInductionIso`
(`Langlands.Representation.Parabolic.HeadTailProductInduction`, induction in
stages) for the published `SegmentProductDatum`. Zelevinsky
(`zelevinsky-1980-induced-ii`, §1.7 and the proof of 6.2 in §6.3) uses
associativity of the product in the same way.

## Conventions

`{p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}` and `T : F.TopologicalData`
are fixed, with `T.topology` installed.
`d : SegmentProductDatum.{uV, uF} T n` (published, `Classification.LanglandsData`)
consists of:

- a length `d.length`;
- segments `d.segments i`, with `∑ deg Δ_i = n`;
- blocks `d.blocks i`, smooth representations of `GL_(deg Δ_i)` with carriers
  in `Type (max uF uV)`.

`d.induced` is the normalized product of the blocks on `d.shape`. For
`h : d.length = k + 2`, the published `BlockShape` data
`d.shape.headIndex h`, `headRank h`, `tailIndex h`, `tailRank h` give the first
block, its rank, the remaining blocks in order, and the sum of their ranks.

## Declarations

- `normalizedProductInductionFunctor_rankCast_obj C h X`: normalized product
  induction on the rank-transported shape `C.rankCast h` equals (as an object)
  the `GL` rank transport along `h` of the product on `C`.
- `binaryNormalizedProductFunctor_obj_eq ha hb A B X h0 h1`: for positive
  ranks `a`, `b` and a family `X` on the binary shape with `X 0 = A` and
  `X 1 = B`, the binary normalized product of `(A, B)` equals the block product
  of `X` (`binaryNormalizedProductFunctor_of_pos`).
- `tail d h` (definition): the segment-product datum, on
  `GL_(d.shape.tailRank h)`, of length `k + 1`, whose segments and blocks are
  those of `d` at `d.shape.tailIndex h j`, i.e. all entries after the first, in
  order. `tail_segments` records `(tail d h).segments j = d.segments (j+1)`
  (with the index cast along `h`). `tail_hasSegmentSocles`: if every block of
  `d` is the segment socle `⟨Δ_i⟩` of its segment (`HasSegmentSocles`), the
  same holds for `tail d h`.
- `nonempty_iso_binary d h`: there is an isomorphism

  ```lean
  d.induced ≅ (generalLinearRankCast T (d.shape.headRank_add_tailRank h)).obj
    ((T.binaryNormalizedProductFunctor (d.shape.headRank h) (d.shape.tailRank h)).obj
      (d.blocks (d.shape.headIndex h), (tail d h).induced))
  ```

  Proof: compose the published `headTailProductInductionIso`, an object
  equality (the two lemmas above), and the published universe-lift
  identification of the first factor.
