# Pole-test combinatorics of multisegments

This module formalizes the combinatorial core of Henniart 2002, §§4.1–4.4
(printed pages 598–600): a multisegment is recovered from how many of its
segments are linked to each test segment of smaller degree. Henniart writes out
part (a) of Théorème 1.7 (Weil–Deligne side) and says part (b) goes the same way.
The module holds only the combinatorics. It states nothing about L-factors,
representations or the Langlands classification, and its recovery step follows a
route different from Henniart's.

## Provenance

Derived. The objects follow Henniart's §4.2. There the order `v(τ, m)` of the
pole at `s = 0` of `L(s, σ ⊗ τ ⊗ St_m)` is the sum of the multiplicities
`f(ρ, n)` of the pairs `(ρ, n)` for which some `j ∈ {1, …, inf(m, n)}` satisfies
`ν^(m+n-1-j) ρ ≃ τ^∨`. In integral coordinates on a twist line, write the segment
`[ρ, ν^(n-1) ρ]` as `[b, e]` and the test (after taking the contragredient) as
`[g, h]`, `h = g + m - 1`. Henniart's condition then becomes
`b ≤ g ≤ e ≤ h` on the same line; this is `IntervalSegment.LinksTo` below. The
equivalence is a short case split on `m ≤ n` or `m > n` and is not formalized
here; tying `LinksTo` to actual pole orders is left to later work.

## Abstract segments (`ι` is a type of lines)

- `IntervalSegment ι`: a line `line : ι`, a lower end point `lower : ℤ` and a
  length `length ≥ 1`. Its upper end point is `upper = lower + length - 1`.
- `IntervalSegment.LinksTo Δ c g k`: `Δ` lies on `c` and
  `Δ.lower ≤ g ≤ Δ.upper < g + k`. In words, the test interval
  `[g, g + k - 1]` on `c` begins in `Δ`, and `Δ` ends in it.
- `IntervalSegment.degree w Δ = Δ.length * w Δ.line` for line weights
  `w : ι → ℕ` (in the application, the rank of the cuspidal data on the line).
- `rawTestCount a c g k`: the number of segments of the multiset `a`, counted
  with multiplicity, that are linked to `[g, g + k - 1]` on `c`.
  `testCount a D` is this count for the test segment `D`.
- `multisetDegree w a`: the sum of the degrees of the segments of `a`.

Elementary lemmas: degrees are additive and positive when all weights are
positive; a segment's degree is at most the total; a multiset whose total degree
is at most the degree of one of its members is that singleton; and
`card a * N ≤ 2 * multisetDegree w a` when every member has `N ≤ 2 · degree`.
`rawTestCount` is additive, and it vanishes on tests of length zero.

## Inversion (Henniart §4.2, formulas (1), (2) and the display after them)

`indicator_eq_alternating` writes the indicator of `Δ = Δ₀` as an alternating
sum of four link indicators, one for each of the tests `[b₀, e₀]`,
`[b₀, e₀ - 1]`, `[b₀ - 1, e₀]` and `[b₀ - 1, e₀ - 1]`. Here `b₀, e₀` are the end
points of `Δ₀`, and the four tests are written by their lower end point and
length. The proof is a case split and integer arithmetic. Summing over a
multiset gives `count_eq_alternating`: the multiplicity of `Δ₀` in `a` equals
`rawTestCount a c b₀ ℓ - rawTestCount a c b₀ (ℓ-1) - rawTestCount a c (b₀-1) (ℓ+1)
+ rawTestCount a c (b₀-1) ℓ`, where `ℓ` is the length of `Δ₀` and `c` its line.
After the change of coordinates above, this corresponds to Henniart's
`f(ρ, m) = w(·, m) - w(·, m+1)` with `w(τ, m) = v(τ, m) - v(ντ, m-1)`.

## Recovery (Henniart §§4.3–4.4)

- `rawTestCount_eq_of_testCount_eq`: agreement on test segments of degree
  `< N` gives agreement of `rawTestCount` on all `(c, g, k)` with `k * w c < N`
  (both sides are zero when `k = 0`).
- `count_eq_of_rawTestCount_eq`: if `(length + 1) * w(line) < N`, all four tests
  of the inversion formula have degree `< N`. So the multiplicities of `Δ` in
  the two multisets agree (Henniart's last sentence of §4.2).
- `rawTestCount_one`: tests of length one count end points
  `endPoint Δ = (Δ.line, Δ.upper)`. `IntervalSegment.point` is the length-one
  segment at a point, and `point (endPoint Δ) = Δ` when `Δ` has length one.
- `eq_of_rawTestCount_eq_of_disjoint` (core step). Let `b` and `b'` be multisets
  with these properties: no element of `b` lies in `b'`; their total degrees are
  equal and at most `N`; every line occurring in them has weight `< N`; and they
  have the same counts on intervals of degree `< N`. Then `b = b'`. Proof: by
  disjointness and the previous lemma, every member `Δ` has
  `N ≤ (length + 1) · w(line) ≤ 2 · degree Δ`, Henniart's inequality §4.3 (3).
  Hence there are at most two members, his (4). Length-one tests at the end
  points of members have degree `w(line) < N`. So the multisets of end points
  agree, and `b` and `b'` have the same number of members. With one member each,
  the equal end points and equal degrees force equal segments. With two
  members, the total degree is `N`, each member has degree `N / 2`, and
  `2 · length · w ≤ (length + 1) · w` forces length one. Such segments are
  determined by their end points. This end-point argument replaces Henniart's
  enumeration of cases in §4.4.
- `eq_singleton_of_le_weight`: a member whose line has weight at least the total
  degree `N` is the whole multiset and has length one.
- `eq_of_testCount_eq` (main abstract theorem). Assume all weights are positive,
  `multisetDegree w a = multisetDegree w a' = N`, and that `a` is not `{Δ}` for
  any `Δ` of length one. If `testCount a D = testCount a' D` for every
  `IntervalSegment` `D` with `D.degree w < N`, then `a = a'`. Proof: every line
  occurring in `a` has weight `< N`, by `eq_singleton_of_le_weight` and the
  hypothesis on `a`. The same holds for `a'`: otherwise `a' = {Δ'}` and all
  counts of `a'` on tests of degree `< N` vanish, while the length-one test at
  the end point of any member of `a` counts that member. Removing the common
  part `a ∩ a'` from both sides (Henniart's reduction at the end of §4.1) and
  applying the core step gives `a - (a ∩ a') = a' - (a ∩ a')`, hence `a = a'`.

## Library segments of cuspidal data

Let `T` be a `F.TopologicalData` for a p-adic field `F`.

- `integralTwistSetoid T`: on `CuspidalDatum T`, `σ ~ ρ` iff `σ = ν^k ρ`
  (`ρ.twist k`) for an integer `k`. `IntegralTwistLine T` is its quotient, and
  `twistLine σ` is the class of `σ`.
- `twistPosition σ : ℤ` is a chosen integer with
  `σ = (twistLine σ).out.twist (twistPosition σ)` (`twistPosition_spec`). The
  Library theorem `Classification.cuspidalIntegralTwistFreeness` (via
  `CuspidalDatum.integralTwist_injective`) makes it unique:
  `twistPosition (c.out.twist k) = k`.
- `lineWeight c = c.out.rank` is positive, and `σ.rank = lineWeight (twistLine σ)`.
- `segmentCoordinates Δ = ⟨twistLine Δ.base, twistPosition Δ.base, Δ.length⟩`.
  It is injective (`segmentCoordinates_injective`), and it is surjective with
  right inverse `segmentOfCoordinates`
  (`segmentCoordinates_segmentOfCoordinates`). It preserves degrees
  (`degree_segmentCoordinates`). The Library predicate
  `Δ.HasIntegralCoordinates (twistLine Δ.base).out (twistPosition Δ.base) upper`
  holds, and `Δ.last` is the twist of the line representative by the upper end
  point (`last_eq_twist_upper`).
- `SegmentPoleLink Δ D`: `D.base ∈ Δ.support ∧ Δ.last ∈ D.support`, that is,
  `D` begins in `Δ` and `Δ` ends in `D`. `segmentPoleLink_iff` shows it is
  equivalent to `LinksTo` on the coordinates. Either condition puts `D.base` on
  the line of `Δ`; then the Library lemma
  `HasIntegralCoordinates.twist_mem_support_iff` turns both memberships into
  inequalities.
- `poleLinkCount a D`: the number of segments `Δ` of the multisegment `a`,
  counted with multiplicity, with `SegmentPoleLink Δ D`. It equals `testCount`
  on the coordinates (`poleLinkCount_eq_testCount`), and
  `multisetDegree lineWeight (a.map segmentCoordinates) = a.degree`.
- `multisegment_eq_of_poleLinkCount_eq`. Let `a` and `a'` be multisegments of
  degree `N`, with `a` not a single segment of length one. If
  `poleLinkCount a D = poleLinkCount a' D` for every segment `D` with
  `D.degree < N`, then `a = a'`. The proof maps both multisegments to
  coordinates, applies `eq_of_testCount_eq`, and uses injectivity of
  `Multiset.map segmentCoordinates`. Twist freeness is the proved Library
  theorem, so the result has no extra hypothesis.

Decidability of the counted predicates comes from `open Classical`.
