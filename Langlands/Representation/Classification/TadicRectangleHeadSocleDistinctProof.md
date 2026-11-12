# Tadić's Lemma 6.3: `L(a(n,d)^ρ) ≇ ⟨a(n,d)^ρ⟩` for `n < d`

Author: Worker 4988.

`Langlands.Classification.TadicRectangleHeadSocle.tadicRectangleHeadSocleDistinct.{uF, uV}`
proves exactly the published proposition
`Langlands.Classification.TadicRectangleHeadSocleDistinct.{uF, uV} F T` of
`Langlands/Representation/Classification/TadicExhaustionLemmasStatement.lean`.
Its outer telescope is
`{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)`,
with `uF` and `uV` independent. It adds no premise. The statement asserts: for
every cuspidal datum `ρ`, all `n, d` with `hd : 0 < d`, `0 < n` and `n < d`,
every `N`, and all `π π' : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear N F.Carrier)`
with `(tadicMultisegment ρ n d hd).IsLanglandsHead π` and
`(tadicMultisegment ρ n d hd).IsZelevinskySocle π'`, there is no isomorphism
`π ≅ π'`. The axioms used are `propext`, `Classical.choice` and `Quot.sound`.

## Source and route

M. Tadić, *Classification of unitary representations in irreducible
representations of general linear group (non-Archimedean case)*, Ann. Sci.
ÉNS (4) 19 (1986), 335–382, literature ID `tadic-1986-unitary`, Lemma 6.3 with
its proof, printed pp.366–367 (PDF pp.33–34). Tadić notes that an equality
`L(a(n,d)^ρ) = ⟨a(n,d)^ρ⟩` gives the standard representations `λ(a(n,d)^ρ)` and
`ζ(a(n,d)^ρ)` a common composition factor. He then compares their Jacquet
modules with respect to the parabolic subgroup attached to the cuspidal
support, using §1 and the proof of Proposition 6.9 of Zelevinsky 1980.

The Lean proof takes a different route, through Bernstein–Zelevinsky
derivatives and supercuspidal supports. A positive-order derivative
constituent of a Zelevinsky socle of `a(n,d)^ρ` has, as support, the cuspidal
content of `a(n,d)^ρ` with some segment *ends* removed. One of a Langlands head
has, segment by segment, terminal truncations, with at least one segment
*beginning* removed. For `n < d` every segment of `a(n,d)^ρ` begins with an
exponent `< 0` and ends with an exponent `> 0`. So the two supports contain
different numbers of data `ν^y ρ` with `y < 0`. Uniqueness of supercuspidal
support then rules out an isomorphism.

## Implemented proof

All declarations are in namespace
`Langlands.Classification.TadicRectangleHeadSocle`, module
`Langlands.Representation.Classification.TadicRectangleHeadSocleDistinctProof`.
Throughout, `P` is a decidable predicate on cuspidal data, `Δ` a segment with
members `Δ.member j = ν^j Δ.base` for `j < Δ.length`, and `L` a number such that
`P (Δ.member j) ↔ j < L` for every `j < Δ.length`, so `P` holds exactly for
the first `L` members of `Δ`.

### Counting lemmas

- `countP_finset_sum`: `countP P (∑ i ∈ s, f i) = ∑ i ∈ s, countP P (f i)` for
  multisets. It is `map_sum` for Mathlib's `Multiset.countPAddMonoidHom`.
- `countP_ofFn_twist`: among `β, νβ, …, ν^(l-1) β`, if `P (ν^j β) ↔ j < L` for
  `j < l`, exactly `min l L` satisfy `P`. Induction on `l`.
- `countP_cuspidalContent`: for `L ≤ Δ.length`, the cuspidal content of `Δ` has
  exactly `L` members satisfying `P`.
- `countP_residualContent`: for `L < Δ.length` and either value of the flag
  `b`, the published `SegmentSocleDerivativeConstituentSupport.residualContent Δ b`
  (the content of `Δ`, or of `Δ` with its end removed) has exactly `L` members
  satisfying `P`. Removing the end removes a member failing `P`, because
  `L < Δ.length`. A shortened singleton has empty content; then `L = 0`.
- `countP_add_le_of_window`: let `1 ≤ L ≤ Δ.length` and `c ≤ 1`. If the underlying
  set of a multiset `s` is the window `{ν^j Δ.base | a ≤ j < Δ.length}`
  (`SegmentHeadSupport.window`) and `card s + c ≤ Δ.length`, then
  `countP P s + c ≤ L`. If `L ≤ a`, no member of the window satisfies `P`, and
  `c ≤ 1 ≤ L`. Otherwise the `Δ.length - L` distinct members `ν^j Δ.base` with
  `L ≤ j` lie in the window and fail `P`. Members of a segment are distinct
  (`SegmentHeadSupport.member_inj`), so they form a nodup sub-multiset of the
  members of `s` failing `P`. Hence `card s ≥ countP P s + (Δ.length - L)`,
  and the bound follows.

### Supports of factor derivatives

- `head_factor_support`: let `H` be a segment head of `Δ` (`T.IsSegmentHead Δ H`),
  `k ≤ Δ.degree`, and `E` an irreducible subquotient of the order-`k`
  derivative of `H`. If `1 ≤ L ≤ Δ.length`, then `E` has a supercuspidal support
  `s` with `countP P s + (if 0 < k then 1 else 0) ≤ L`. The published
  `segmentHeadDerivativeSupportTruncation` gives a support `s` whose underlying
  set is the support of an optional terminal truncation of `Δ`.
  `SegmentHeadSupport.exists_terminal_iff` turns this set into a window
  `{ν^j Δ.base | a ≤ j < Δ.length}`. Every member of `s` is a twist of
  `Δ.base`, so has rank `Δ.rank`. The rank equation in
  `IsSupercuspidalSupport` then gives `card s * Δ.rank = Δ.degree - k`, with
  `Δ.degree = Δ.length * Δ.rank` and `Δ.rank > 0`. So `card s ≤ Δ.length`, and
  `card s < Δ.length` when `k > 0`. `countP_add_le_of_window` concludes.
- `socle_factor_support`: let `S` be a segment socle of `Δ`, `k ≤ Δ.degree`, and
  `E` an irreducible subquotient of the order-`k` derivative of `S`. If
  `L < Δ.length`, then `E` has a support `s` with `countP P s = L`. The published
  `SegmentSocleDerivativeConstituentSupport.segment_support` gives the support
  `residualContent Δ b` for some flag `b`; `countP_residualContent` counts it.

### Combinatorics of `a(n,d)^ρ`

- `exists_negative_prefix`: let `n < d` and `Δ ∈ tadicMultisegment ρ n d hd`. Let
  `P c` mean `∃ y < 0, c = ν^y ρ`. Then there is `L` with `1 ≤ L < Δ.length` and
  `P (Δ.member j) ↔ j < L` for all `j < Δ.length`. By `mem_tadicMultisegment`,
  `Δ` is the centered segment of length `d` at `x = j₀ - (n-1)/2` with
  `j₀ < n`. Its member `j` is `ν^(j + x - (d-1)/2) ρ`. Twisting is injective
  (`cuspidalDatum_twist_injective`), so `P (Δ.member j)` holds iff
  `j < (d-1)/2 - x`. Take `L = ⌈(d-1)/2 - x⌉₊`. Then `j < L` iff
  `j < (d-1)/2 - x`. From `j₀ + 1 ≤ n` and `n + 1 ≤ d` follow
  `(d-1)/2 - x > 0`, so `L ≥ 1`, and `(d-1)/2 - x ≤ d - 1`, so `L < d`.
- `sum_segments_eq`: for a segment product datum `D` and `f : Segment → ℕ`,
  `∑ i, f (D.segments i)` is the sum of `f` over `D.multisegment`.

### Main theorem

Fix `ρ, n, d, hd, 0 < n, n < d, N, π, π'`, the head and socle hypotheses, and
an isomorphism `e : π ≅ π'`. Let `P c := ∃ y < 0, c = ν^y ρ`, and let
`Lf Δ` count the members of `Δ`'s cuspidal content satisfying `P`.

1. `padicUnitaryAdditiveCharacterExists` supplies a unitary additive character
   `ψ`. `N = n * (d * rank ρ) > 0` by
   `tadicMultisegment_rank_eq_of_isZelevinskySocle`.
2. The head hypothesis supplies a segment product datum `dH` with multisegment
   `a(n,d)^ρ`, segment-head blocks, and `π` an irreducible quotient of the
   product of the blocks. The socle hypothesis supplies `dS` with multisegment
   `a(n,d)^ρ`, segment-socle blocks, and `π'` a subrepresentation of their
   product. So `π` and `π'` are subquotients of the respective products.
3. `chooseGeneralLinearHighestDerivativeOrder` gives a highest order
   `w.order > 0` with a nonzero derivative of `π`. That derivative has finite
   length (`generalLinearDerivativeFiniteLength`), so it has an irreducible
   subrepresentation `D` (`SegmentHeadSupport.exists_irreducible_subrepresentation`).
   `D` is a subquotient of the order-`w.order` derivative of `π`, and,
   transporting along the derivative functor's image of `e`, of that of `π'`.
4. `ProductDerivativeSupport.supportDataOfSubquotient` is applied twice to `D`.
   On the head side the factor condition is
   `countP P s + (if 0 < k then 1 else 0) ≤ Lf (dH.segments i)`, supplied by
   `head_factor_support` with `exists_negative_prefix` and
   `countP_cuspidalContent`. On the socle side it is
   `countP P s = Lf (dS.segments i)`, supplied by `socle_factor_support`.
   Finite length of each factor derivative is
   `generalLinearDerivativeFiniteLength`, since each block is irreducible. Each
   application yields, for every block `i`, an order `k_i` and a support `s_i`
   with the factor condition, `∑ k_i = w.order`, and `∑ s_i` a supercuspidal
   support of `D`.
5. The two supports of `D` agree. If `N - w.order > 0`, this is
   `glSupercuspidalSupportUniqueness`. Otherwise every support of `D` is `0` by
   `SegmentHeadSupport.pos_of_isSupercuspidalSupport`.
6. Count `P` in the common support with `countP_finset_sum`. The socle side
   gives `∑_i Lf (dS.segments i)`. On the head side, `∑ k_i = w.order > 0`
   gives some `k_i > 0`, so the head count is at most
   `∑_i Lf (dH.segments i) - 1`. Both data have multisegment `a(n,d)^ρ`, so by
   `sum_segments_eq` the two sums of `Lf` agree. `omega` derives the
   contradiction.

The proof uses neither the positivity of `n` beyond `N > 0`, nor unitarity of
`ρ`, nor any ordering of the segments. All representations, cuspidal data and
segments are at universe `max uF uV`, as in the statement.
