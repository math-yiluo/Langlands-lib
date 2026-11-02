# Splitting the earlier segment of an overlapping precedence pair

Author: Worker 1033.

Step (2) of Zelevinsky 1980, Proposition 4.6 (printed p. 186) uses the segment
`Δ' \ Δ∩` when `Δ'` precedes `Δ` and the two overlap. This module proves the
segment facts behind that step. The proof is an internal derivation in
integral coordinates. It lives in the namespace
`Langlands.Classification.QuotientHom`. This is a supporting lemma for the exact
proof task ba6ec030, and it does not prove the target statement by itself.

## Statement

`exists_overlap_split hp hs` assumes:

- `hp : Δ'.Precedes Δ`;
- `hs : Δ.IsUnionIntersectionReplacement Δ' U (some J)`, so that
  `U.support = Δ.support ∪ Δ'.support` and `J` is the intersection.

It produces `q` with `0 < q < Δ'.length` such that, with
`init = Δ'.initial q hq`:

1. `Δ'.terminal q hqm = J`;
2. `init.Precedes Δ`;
3. `init.IsJuxtaposed Δ`;
4. `Δ.IsUnionIntersectionReplacement init U none`;
5. `U.degree = Δ.degree + init.degree`.

## Proof

The proof uses the published `cuspidalIntegralTwistFreeness` (`hfree`). The
replacement relation is symmetric in its two segments up to commuting `∪` and
`∩`. With `Δ'` first, the published `IsUnionIntersectionReplacement.coordinates`
gives a cuspidal datum `ρ` and integers `a, b, c, d` with:

- `Δ' = [a, b]` and `Δ = [c, d]` in integral coordinates over `ρ`;
- `a < c` and `b < d`;
- `U = [a, d]`;
- `J = [c, b]`, from which `c ≤ b` (`HasIntegralCoordinates.lower_le_upper`).

Put `q = c - a`, so `0 < q < Δ'.length`. Twisting the base of `Δ'` by `k` is
twisting `ρ` by `a + k` (`CuspidalDatum.twist_twist`). It follows that
`Δ'.terminal q hqm` has coordinates `[c, b]` and `init` has coordinates
`[a, c - 1]`. Then:

- the published `HasIntegralCoordinates.precedes_iff` gives `init ≺ Δ`;
- `init` and `Δ` are disjoint, by `mem_support_iff` and
  `twist_mem_support_iff` and the inequality `c - 1 < c`;
- `support_union_eq` and `support_eq_iff` give
  `U.support = Δ.support ∪ init.support`, while disjointness gives an empty
  intersection. This is the replacement `(U, none)`;
- two segments with equal supports are equal (`eq_of_support_eq`), so
  `Δ'.terminal q hqm = J`;
- all four segments have the rank of `ρ`, and
  `U.length = Δ.length + q`. Hence
  `deg U = deg Δ + q · rank = deg Δ + deg init`.

Linkage of `init` and `Δ` comes from `Precedes.isLinked`, and with
disjointness this gives juxtaposition.
