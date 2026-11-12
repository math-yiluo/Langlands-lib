# Combinatorics of the rectangle `a(n,d)` (helper for Tadić's Proposition 3.8)

Author: Worker 4021. Module
`Langlands.Representation.Classification.TadicRectanglePrimeCombinatorics`, namespace
`Langlands.Classification.TadicRectanglePrime`. It is a helper module of the proof
`Langlands.Classification.TadicRectanglePrime.tadicRectangleSoclePrime` of
`Langlands.Classification.TadicRectangleSoclePrime`. It contains definitions of
multisegments and purely combinatorial theorems about them; it adds no hypothesis and uses
only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Provenance

M. Tadić, *Classification of unitary representations in irreducible representations of
general linear group (non-Archimedean case)*, Ann. Sci. ÉNS (4) 19 (1986), literature ID
`tadic-1986-unitary`:

- §3.1 (printed p.352, PDF p.19): with `Δ[d] = [ν^(-(d-1)/2), ν^((d-1)/2)]`,
  `a(n,d)` consists of the `n` twists `ν^((n-1)/2) Δ[d], ν^((n-3)/2) Δ[d], …,
  ν^(-(n-1)/2) Δ[d]`, segments of length `d`; in the Library `a(n,d)^ρ` is
  `tadicMultisegment ρ n d hd`, the segments `ν^(j-(n-1)/2) Δ[d]^ρ`, `0 ≤ j < n`.
- §3.4 (printed p.353, PDF p.20): with `a(n,d)^ρ = (Δ_1, …, Δ_n)`,
  `Δ_1 → Δ_2 → ⋯ → Δ_n`, Lemma 3.4 says that every `b ≤ a(n,d)^ρ` contains each `Δ_i`
  at most once.
- §3.7 (printed p.354, PDF p.21): `a_{k,k+1}` replaces `Δ_k, Δ_(k+1)` by
  `Δ_k ∪ Δ_(k+1)` and `Δ_k ∩ Δ_(k+1)`, and nothing lies strictly between `a_{k,k+1}`
  and `a(n,d)^ρ`.
- The degree count on printed p.355 (PDF p.22), here replaced by the weight count
  `weight_ne_of_le_adj`.

Here Zelevinsky's order `≤` is replaced by the Library's rank order
`Multisegment.RankLE` (`b ≼ a`: same cuspidal content and
`containmentCount I a ≤ containmentCount I b` for every segment `I`, where
`containmentCount I a` counts the segments of `a` containing `I`). This is the order in
which the Library proves Zelevinsky's Theorem 7.1, so Tadić's statements are proved here
for it. The definitions `seg`, `rect`, `restIdx`, `rest`, `capMs`, `adj` are internal
coordinates; `tadicMultisegment_eq_rect` and `replacement_eq` tie them to the Library's
`tadicMultisegment` and to `Segment.IsUnionIntersectionReplacement`.

## Definitions

Fix a cuspidal datum `σ`.

- `seg σ i l`: the segment with base `ν^i σ` (`σ.twist i`) and length `l + 1`, i.e.
  `[ν^i σ, ν^(i+l) σ]`. Writing lengths as `l + 1` avoids positivity side conditions.
- `rect σ n e`: the multisegment of the `n` segments `Δ_j = seg σ j e`, `j < n`.
- `restIdx n k`, `rest σ n k e`: the indices `j < n` other than `k, k + 1`, and the
  corresponding segments `Δ_j`.
- `capMs σ k e`: the intersection `Δ_k ∩ Δ_(k+1) = seg σ (k+1) (e-1)` as a one-element
  multisegment when `e ≥ 1`, and `0` when `e = 0` (then the intersection is empty).
- `adj σ n k e`: `seg σ k (e+1)` (the union `Δ_k ∪ Δ_(k+1)`) added to `capMs σ k e` and
  `rest σ n k e`. This is Tadić's `a_{k,k+1}`.

## Results

### Segments in positions

- `seg_base`, `seg_length`, `seg_member`: `(seg σ i l).member j = ν^(i+j) σ`.
- `seg_subset_iff`: `[i, i+l] ⊆ [i', i'+l']` iff `i' ≤ i` and `i + l ≤ i' + l'`, using
  injectivity of natural twists (`twist_natCast_injective`).
- `seg_eq_seg_iff`, `seg_injective`: `seg σ i l = seg σ i' l'` iff `i = i'`, `l = l'`.
- `exists_eq_seg_of_subset`: a segment contained in `seg σ i l` is some `seg σ t l'`.
- `eq_of_support_eq`: segments with equal supports are equal.
- `seg_support_union`: `seg σ k (e+1)` has support `Δ_k ∪ Δ_(k+1)`.
- `seg_precedes`: `Δ_k` precedes `Δ_(k+1)` (linked, base shifted by `ν^1`).

### The rectangle and its neighbour

- `tadicMultisegment_eq_rect`: `tadicMultisegment ρ n d hd =
  rect (ν^(-(n-1)/2 - (d-1)/2) ρ) n (d-1)`. Segment `j` of `tadicMultisegment` is the
  centred segment of length `d` at `j - (n-1)/2`, whose base is
  `ν^(j - (n-1)/2 - (d-1)/2) ρ`.
- `rect_succ`, `toFinsupp_rect`: the monomial of `rect σ n e` is
  `∑_{j<n} single (Δ_j) 1`.
- `nodup_restIdx`, `mem_restIdx`, `rect_eq`, `rect_eq_pair_add`: `rect σ n e` is
  `{Δ_(k+1), Δ_k} + rest σ n k e` for `k + 1 < n`.
- `count_rest`, `exists_of_mem_rest`: `rest` contains `Δ_j` once if `j ∈ restIdx n k`
  and otherwise not, and consists of segments `Δ_j`, `j < n`.
- `adj_eq_add`: `adj = (seg σ k (e+1) ::ₘ capMs σ k e) + rest`.
- `replacement_eq`: if `(seg σ (k+1) e).IsUnionIntersectionReplacement (seg σ k e) U I`,
  then the multisegment `U :: I.toList` is `seg σ k (e+1) ::ₘ capMs σ k e`. The union
  is identified by `seg_support_union`. The case `I = none` forces `e = 0`, since for
  `e ≥ 1` the point `ν^(k+1) σ` lies in both segments. For `I = some J`, `J` lies in
  `Δ_k` and so is `seg σ t l`; the inclusions of `J` and of `seg σ (k+1) (e-1)` in
  the intersection give `t = k + 1`, `l = e - 1`.

### Containment counts and the rank order

- `containmentCount_capMs`, `containmentCount_adj`: for every segment `I`,
  `containmentCount I (adj) = containmentCount I (rect) + [I = seg σ k (e+1)]`. If `I`
  lies in the union, it is some `seg σ t l` and the identity is arithmetic on positions;
  otherwise `I` lies in none of the changed segments.
- `cuspidalContent_eq_of_containmentCount`, `containmentCount_eq_of_cuspidalContent_eq`:
  equal cuspidal content is equivalent to equal containment counts of one-element
  segments (`containmentCount_singletonSegment`).
- `rankLE_adj`, `adj_ne_rect`: `adj ≼ rect` and `adj ≠ rect`.
- `eq_adj_of_rankLE`: if `adj ≼ b ≼ rect` and `b ≠ rect`, then `b = adj`. All counts of
  `b` other than at the union are squeezed to those of `rect`; at the union the count is
  that of `rect` or one more. In the first case `b = rect` by `eq_of_containmentCount_eq`,
  excluded; in the second `b = adj` by the same lemma.

### Tadić's Lemma 3.4

- `count_add_containmentCount_le`: for every multisegment `x`,
  `count Δ_j x + containmentCount [ν^(j+e) σ, ν^(j+e+1) σ] x ≤
  containmentCount {ν^(j+e) σ} x`: each copy of `Δ_j` contains its end `ν^(j+e) σ` but
  not the two-element segment starting there.
- `containmentCount_rect_le`: in `rect σ n e`, the count of `{ν^(j+e) σ}` exceeds that of
  `[ν^(j+e) σ, ν^(j+e+1) σ]` by at most `1` (by `0` if `j ≥ n`). Induction on `n`.
- `count_le_one_of_rankLE` (**Lemma 3.4**): if `x ≼ rect σ n e`, then `x` contains each
  `Δ_j` at most once. The one-element count is the same for `x` and `rect` (equal
  cuspidal content), and the two-element count of `x` is at least that of `rect`.
  This is Tadić's end-point counting argument.

### Weights

- `weight_toFinsupp`: for the weight `S ↦ S.length`, the weight of the monomial of a
  multisegment `x` is `card x.cuspidalContent`.
- `count_adj_left`, `count_adj_right`, `count_adj_of_ne`: `adj` contains neither `Δ_k`
  nor `Δ_(k+1)`, and contains `Δ_j` exactly once for every other `j < n`.
- `card_cuspidalContent_ne_of_le`: a submultiset of `seg σ k (e+1) ::ₘ capMs σ k e` has
  cuspidal content of size `0`, `e`, `e + 2` or `2e + 2`, never `e + 1`.
- `weight_ne_of_le_adj`: no monomial `ν ≤ X^{adj}` with `ν (Δ_j) = 0` for all `j < n`
  has weight `e + 1`. Such a `ν` only uses the union and the intersection, since every
  segment of `rest` is some `Δ_j`; `card_cuspidalContent_ne_of_le` concludes. This holds
  for `e = 0` as well, where the intersection is absent.
