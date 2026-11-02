# Containment counts and the rank order on multisegments

This module is pure combinatorics on the published segments and multisegments of
`Langlands/Representation/Classification/Segments.lean`. It defines a partial order
on multisegments, the *rank order*, and proves the facts that the proof of
Zelevinsky 1980, Theorem 7.1, needs from an order:

- it is a partial order;
- its strict part is well founded;
- it satisfies the combinatorial step `(*)` of Ze80 §7.4.

It does not prove anything about representations.

All declarations are in namespace `Langlands.PadicField.TopologicalData` (sub-namespaces
`CuspidalDatum`, `Segment`, `Multisegment`). The parameters are
`F : PadicField.{uF} p` and `T : F.TopologicalData`; the universes `uF`, `uV` are
independent. A segment `Δ` has a beginning `Δ.base`, a length `Δ.length > 0` and
members `Δ.member i = ν^i Δ.base` (published definitions). A multisegment is a
`Multiset` of segments.

## Provenance: why a rank order

Ze80 §7.1 orders multisegments by *elementary operations*: `b ≤ a` when `b` comes
from `a` by repeatedly replacing a linked pair `{Δ, Δ'}` by `{Δ ∪ Δ', Δ ∩ Δ'}`.
In §7.4 it reduces the remaining half of Theorem 7.1 to the statement

> `(*)` If `a, b` have the same cuspidal content and `b⁻ ≤ a'` for some `a'`
> subordinate to `a`, then `b ≤ a`.

Here `a'` is *subordinate* to `a` when it comes from `a` by replacing some segments
`Δ` by `Δ⁻`, and `b⁻` replaces every segment of `b` by `Δ⁻` (dropping empty ones).
Ze80 omits the proof of `(*)` as "easy, purely combinatorial".

This module does not formalize Zelevinsky's order. It uses instead the order given by
*containment counts*. For a segment `I` and a multisegment `a`, the count `r_I(a)` is
the number of segment occurrences of `a` whose support contains the support of `I`.
The rank order `b ≼ a` asks that `a` and `b` have the same cuspidal content and that
`r_I(a) ≤ r_I(b)` for every segment `I`. For the proof of Theorem 7.1 an order only
needs the three properties listed at the top. For the rank order, `(*)` becomes a
counting argument, which is proved here. The intended use is the
proof of `SegmentPolynomialComparisonStatement` (Ze80 Cor. 7.5) by induction along
`wellFounded_rankLT`.

The relation between the rank order and Zelevinsky's order is not used and is not
formalized here.

## Segments

- `CuspidalDatum.twist_natCast_twist_natCast`: `ν^j (ν^i ρ) = ν^(i+j) ρ` for natural
  `i, j`.
- `CuspidalDatum.twist_natCast_injective`: `ν^i ρ = ν^j ρ` forces `i = j`. It follows
  from the published integral twist-freeness
  `Classification.cuspidalIntegralTwistFreeness`.
- `Segment.member_injective`: members of a segment at different positions differ.
  `Segment.member_twist_natCast`: `ν^j (Δ.member i) = Δ.member (i + j)`.
- `Segment.ext_base_length`: a segment is determined by its beginning and its length.
- `Segment.support_subset_iff`: `I.support ⊆ Δ.support` iff `I.base = Δ.member i` for
  some `i` with `i + I.length ≤ Δ.length`. The forward direction compares the
  positions of the beginning and of the end of `I` inside `Δ` by `member_injective`.
  The converse is the published `support_subset_of_base_shift`.
- `Segment.length_le_of_support_subset` and
  `Segment.eq_of_support_subset_of_length_le`: a segment contained in a segment of at
  most its length equals it.
- `Segment.dropLastNonempty_support_subset`: `Δ⁻ ⊆ Δ`, for the published truncation
  `dropLastNonempty` of a segment of length at least two.
  `Segment.dropLastNonempty_support_subset_iff`: for `I` and `Δ` of length at least
  two, `I⁻ ⊆ Δ⁻` iff `I ⊆ Δ`. Both truncations keep the beginning and shorten the
  length by one.
- `Segment.cuspidalContent_nodup`: the published cuspidal content of one segment has
  no repetition.
- `Segment.singletonSegment_support_subset_iff`: the published one-member segment
  `T.singletonSegment ρ` is contained in `Δ` iff `ρ ∈ Δ.support`.
  `Segment.eq_singletonSegment_of_length_eq_one`: a segment of length one is
  `T.singletonSegment` of its beginning.

## Truncation of a multisegment

- `Multisegment.dropLast a` is Zelevinsky's `a⁻`. It is `Multiset.filterMap` of the
  published `Segment.dropLast : Segment → Option Segment`, so one-member segments
  disappear and the other segments lose their end.
  `dropLast_coe` identifies it on a list with the published `Segment.dropLastList`.
  `dropLast_zero`, `dropLast_add`, `dropLast_cons_of_one_lt` and
  `dropLast_cons_of_length_eq_one` are the computation rules.
  A multisegment subordinate to `a = c + S` is written `c + S.dropLast`.

## Containment counts

- `Multisegment.containmentCount I a := a.countP (fun Δ => I.support ⊆ Δ.support)`,
  with the classical decidability instance. Rules: `containmentCount_zero`,
  `containmentCount_add`, `containmentCount_cons` (adds `1` exactly when
  `I ⊆ Δ`), `containmentCount_pos_iff`, `containmentCount_le_card`.
- `containmentCount_mono`: if `I ⊆ J` then `r_J(a) ≤ r_I(a)`.
- `containmentCount_singletonSegment`: `r_[ρ](a)` is the multiplicity of `ρ` in the
  published cuspidal content `a.cuspidalContent`. Each segment containing `ρ`
  contributes `ρ` exactly once, by `cuspidalContent_nodup`.
- `containmentCount_dropLast`: for `I` of length at least two,
  `r_{I⁻}(a⁻) = r_I(a)`. Segments of length one contain no such `I` and vanish in `a⁻`.
  The others satisfy `I⁻ ⊆ Δ⁻ ↔ I ⊆ Δ`.
- `containmentCount_le_subordinate`: for `I` of length at least two,
  `r_I(c + S) ≤ r_{I⁻}(c + S⁻)`. On `S` this is `containmentCount_dropLast`; on `c`
  it is monotonicity, since `I⁻ ⊆ I`.
- `containmentCount_eq_count_of_maximal`: if no segment of `a` is longer than `Δ`,
  then `r_Δ(a)` is the multiplicity of `Δ` in `a`.
- `eq_of_containmentCount_eq`: two multisegments with the same containment counts
  are equal. The proof is by induction on the total number of segments. A segment
  `Δ` of maximal length in `a + b` has the same multiplicity in `a` and `b`, by the
  previous lemma. It occurs in both, and erasing it from both preserves the
  equality of all counts.

## The rank order

- `Multisegment.RankLE b a := b.cuspidalContent = a.cuspidalContent ∧
  ∀ I, containmentCount I a ≤ containmentCount I b`.
- `RankLE.refl`, `RankLE.trans`, `RankLE.antisymm` (from
  `eq_of_containmentCount_eq`): a partial order.
- `RankLE.of_dropLast` is Ze80's step `(*)` for this order. Hypotheses:
  `a = c + S`, `b.cuspidalContent = a.cuspidalContent` and
  `RankLE b.dropLast (c + S.dropLast)`. Conclusion: `RankLE b a`. Here `b.dropLast`
  is `b⁻` and `c + S.dropLast` is subordinate to `a`. Proof, for a segment `I`:
  - If `I` has length at least two, then
    `r_I(a) ≤ r_{I⁻}(c + S⁻) ≤ r_{I⁻}(b⁻) = r_I(b)`, by
    `containmentCount_le_subordinate`, the hypothesis and `containmentCount_dropLast`.
  - If `I = [ρ]` has length one, both counts are the multiplicity of `ρ` in the
    common cuspidal content.
- `RankLE.degree_eq`: rank-comparable multisegments have the same published
  `degree`, via the published `sum_rank_cuspidalContent`.

## Well-foundedness

- `candidateSegments φ`: the finite set of segments beginning at a member of the
  multiset `φ` with length at most `card φ`. `mem_candidateSegments`: every segment
  contained in a segment of `a` lies in `candidateSegments a.cuspidalContent`. Its
  beginning is in the content (`cuspidalContent_le_of_mem`). Its length is at most
  `card a.cuspidalContent`.
- `rankMeasure φ a := ∑ I ∈ candidateSegments φ, containmentCount I a`.
  `rankMeasure_le`: `rankMeasure a.cuspidalContent a` is at most
  `card (candidateSegments a.cuspidalContent) * card a.cuspidalContent`. Each count
  is at most the number of segments (`card_le_card_cuspidalContent`).
- `rankMeasure_lt`: if `RankLE b a` and `b ≠ a`, then some count of `b` exceeds
  that of `a` (antisymmetry), at a candidate segment. Hence
  `rankMeasure a.cuspidalContent a < rankMeasure a.cuspidalContent b`.
- `wellFounded_rankLT`: the relation `fun b a => RankLE b a ∧ b ≠ a` on
  `Multisegment.{uV, uF} T` is well founded. It is a subrelation of the inverse
  image of `<` on `ℕ` under
  `a ↦ card (candidateSegments a.cuspidalContent) * card a.cuspidalContent − rankMeasure a.cuspidalContent a`.
  The bound depends only on the cuspidal content, which is shared by related
  multisegments.

## Sources

Zelevinsky 1980, *Induced representations of reductive p-adic groups II*, §7.1
(the order and Theorem 7.1) and §7.4 (subordinate multisegments, `a⁻`, statement
`(*)`), printed pp. 192–193. The rank order, the containment counts and all proofs
here are this module's own. Zelevinsky's order is not formalized.
