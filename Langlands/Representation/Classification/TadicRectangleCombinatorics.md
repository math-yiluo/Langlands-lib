# `a(d,n)^ρ` is not a sum of smaller Tadić pieces

Author: Worker 1792. Module
`Langlands.Representation.Classification.TadicRectangleCombinatorics`, namespace
`Langlands.Classification`. Everything is proved; there are no hypotheses of
theorem type, no axioms and no `sorry`.

This is the combinatorial content of Tadić's step "by the preceding
considerations `L(a(n,d)^ρ) ∉ I(Ĝ_m)`" in the proof of Theorem A.10 (1986,
printed p.379): the Langlands form `L(∑ a_i)` of a product of members of
`X_(m-1)` cannot be `L(a(n,d)^ρ)`, because `a(n,d)^ρ` is not such a sum `∑ a_i`.

## Declarations

- `IsTadicHeadPiece m c`: `c` is `a(u,v)^τ` (that is, `tadicMultisegment τ u v hv`)
  with `u, v > 0`, `τ` unitary and degree at most `m`, or `c` is the twist
  `ν^s a(u,v)^τ` (`Multisegment.twist s`) with `u, v > 0`, `τ` unitary and
  `0 < |s| < 1/2`. These are the multisegments of the Langlands heads that make up
  members of `X_m` (see `TadicHeadPieceFactorization`).
- `mem_tadicMultisegment`: the segments of `a(n,d)^ρ` are the
  `ν^(j - (n-1)/2) Δ[d]^ρ`, `j < n`.
- `tadicCenteredSegment_twist_eq`: `ν^s (ν^x Δ[v]^τ) = ν^y Δ[n]^ρ` with `ρ, τ`
  unitary forces `τ = ρ`, `v = n` and `s + x = y` (compare lengths and bases, then
  `cuspidalDatum_eq_of_twist_eq_of_isUnitary`).
- `tadicCenteredSegment_injective`: `ν^x Δ[n]^ρ = ν^y Δ[n]^ρ` forces `x = y`.
- `tadicCentralCount ρ n hn a`: the number of segments of `a`, with multiplicity,
  equal to `ν^0 Δ[n]^ρ` or to `ν^(1/2) Δ[n]^ρ` (a classical `Multiset.countP`). It is
  additive (`tadicCentralCount_add`, `tadicCentralCount_sum`).
- `tadicCentralCount_tadicMultisegment`: for `u > 0`, `a(u,n)^ρ` has exactly one
  such segment. Its centers are `j - (u-1)/2`, `j < u`, and exactly `j = ⌊u/2⌋`
  gives a center in `{0, 1/2}`.
- `not_sum_tadicHeadPieces`: let `ρ` be unitary, `n, d > 0` and
  `m < deg a(d,n)^ρ`. No finite family `c : Fin k → Multisegment` of Tadić head
  pieces for `m` has `∑ i, c i = a(d,n)^ρ`.

## Proof of `not_sum_tadicHeadPieces`

Each `c i` is contained in `a(d,n)^ρ`, so each of its segments is a segment
`ν^y Δ[n]^ρ`, `y = j - (d-1)/2`, of `a(d,n)^ρ`.

- A twisted piece `ν^s a(u,v)^τ` contains `ν^s ν^x Δ[v]^τ` with
  `x = -(u-1)/2`; matching it gives `τ = ρ`, `v = n` and `s = y - x`, so
  `2s = 2j + u - d` is an integer. Since `0 < |2s| < 1` this is impossible.
- An untwisted piece `a(u,v)^τ` similarly has `τ = ρ` and `v = n`, so it is
  `a(u,n)^ρ`, with central count `1`.

Additivity of the central count gives `1 = k` (the count of `a(d,n)^ρ` is `1`).
Then `a(d,n)^ρ = c 0` has degree at most `m`, contradicting `m < deg a(d,n)^ρ`.
